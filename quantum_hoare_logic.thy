theory quantum_hoare_logic
imports Main  Matrix 
begin

(*The datatype for representing syntax of quantum programs*)
datatype
com=SKIP
|Init "nat" "number"
|Utrans "Mat" "number"
|Seq "com" "com"          ("(_;/ _)"   [60,61] 60  )
|Cond "(Mat * com * Mat) list"  
|While "Mat" "Mat" "com" "Mat" 


primrec M_sum::"(Mat*com*Mat) list\<Rightarrow>Mat"where
"M_sum [] =zero"|
"M_sum (a#M) =mat_add (mat_mult (dag (fst a) ) (fst a)) (M_sum M )"
primrec sum::"nat list\<Rightarrow>nT\<Rightarrow>Mat\<Rightarrow>Mat" where
"sum [] f1 p=p"|
"sum (b#nl) f1 p = mat_add (mat_mult (mat_mult (f1 b) p) (dag (f1 b)) ) (sum nl f1 p )"
primrec sum_t::"nat list\<Rightarrow>nT\<Rightarrow>Mat\<Rightarrow>Mat"where
"sum_t [] f1 p=p"|
"sum_t (b#nl) f1 p = mat_add (mat_mult (mat_mult (dag (f1 b)) p)  (f1 b) ) (sum_t nl f1 p )"
primrec sum_1::"nat list\<Rightarrow>nT\<Rightarrow>Mat" where
"sum_1 [] f1 =I"|
"sum_1 (b#nl) f1 =mat_add (mat_mult (f1 b) (dag (f1 b))) (sum_1 nl f1)"
primrec sum_2::"nat list\<Rightarrow>nT\<Rightarrow>Mat" where
"sum_2 [] f1 =I"|
"sum_2 (b#nl) f1 =mat_add (mat_mult (dag (f1 b))  (f1 b)   ) (sum_2 nl f1)"
(*u a b =ab(dag a) *)
definition u::"Mat\<Rightarrow>Mat\<Rightarrow>Mat"where
"u a b= mat_mult (mat_mult a b) (dag a)"
(*uu a b =(dag a)ba *)
definition uu::"Mat\<Rightarrow>Mat\<Rightarrow>Mat"where
"uu a b= mat_mult (mat_mult (dag a) b)  a"
primrec accum::"(Mat*com*Mat) list\<Rightarrow>Mat" where
"accum [] =zero"|
"accum (a#M) = mat_add (snd (snd a)) (accum M)"

inductive denofun::"com\<Rightarrow>Mat\<Rightarrow>Mat\<Rightarrow>bool" where
"denofun SKIP p p"
|"denofun (Utrans U n) p ( mat_mult (mat_mult U p) (dag U) ) "
|"denofun  (Init m n) p (sum (h m) f p )"
|"denofun s1 p p''\<Longrightarrow>denofun s2 p'' p'\<Longrightarrow>denofun (s1;s2) p p'"
|"\<forall>a b c. (a,b,c)\<in>set mcl\<longrightarrow>denofun b (u a p) c\<Longrightarrow>denofun (Cond mcl) p (accum mcl)"
|"denofun s (u m1 p) p''\<Longrightarrow>denofun (While m0 m1 s Q) p'' p'\<Longrightarrow>
                                        denofun (While m0 m1 s Q) p (mat_add (u m0 p) p' )"
inductive_cases [elim!]:
"denofun (SKIP) s s'" 
"denofun (s1;s2) s s'" 
 "denofun (Utrans U n) s s'"
"denofun (Init m n) s s'"
"denofun (Cond mcl) s s'"

fun rank :: "com\<Rightarrow>nat" where
"rank SKIP =1"|
"rank (Utrans U n) =1"|
"rank (Init m n) =1"|
"rank (s1;s2) =1+ rank s2 + (rank s1 )"|
"rank (Cond mcl) =  (case mcl of [] \<Rightarrow> 1
  | mc # mcr \<Rightarrow> 1+rank (fst (snd mc)) + rank (Cond mcr)) "|
"rank  (While  m0 m1 s Q )= 1 + rank s"
lemma wellDefined_aux: "(x, xa, xb) \<in> set mcl \<Longrightarrow>
       (xc, xd) \<in> Basic_BNFs.snds (x, xa, xb) \<Longrightarrow>
       xe \<in> Basic_BNFs.fsts (xc, xd) \<Longrightarrow> rank xe < (case mcl of [] \<Rightarrow> 1 | mc # mcr \<Rightarrow> 1 + rank (fst (snd mc)) + rank (Cond mcr))"
apply (induct mcl, auto)
by (metis fst_conv fsts.cases not_add_less1 not_less_eq sndI snds.cases)

(*the conditions that the commands should meet iff they are well-defined  *)
function wellDefined :: "com\<Rightarrow>bool" where
"wellDefined SKIP =True"|
"wellDefined (Utrans a n) = (UMat a)"|
"wellDefined (Init m n) =((sum_1 (h m) f =I)\<and>(sum_2 (h m) f=I))"|
"wellDefined (s1;s2) = (wellDefined (s1) & wellDefined (s2))"|
"wellDefined (Cond mcl) = ((M_sum mcl=I) \<and> 
(\<forall>a aa b aaa ba xaaa. (a, aa, b) \<in> set mcl \<longrightarrow>
       (aaa, ba) \<in> Basic_BNFs.snds (a, aa, b) \<longrightarrow>
       xaaa \<in> Basic_BNFs.fsts (aaa, ba) \<longrightarrow> wellDefined xaaa))"|
"wellDefined  (While  m0 m1 s Q )=((mat_add (mat_mult (dag m0) m0)  (mat_mult (dag m1) m1) =I)  \<and> (wellDefined s)  )  "
by  pat_completeness auto
termination 
apply (relation "measure (\<lambda>(c).rank c)", auto)
apply (rule wellDefined_aux, auto)
done
definition valid::"Mat\<Rightarrow>com\<Rightarrow>Mat\<Rightarrow>bool" where
"valid P S Q=(\<forall>\<rho> p. positive \<rho>\<longrightarrow>denofun S \<rho> p\<longrightarrow>Tr (mat_mult P \<rho>)\<le>Tr (mat_mult Q p)+Tr \<rho>-Tr p)"
definition svalid::"Mat\<Rightarrow>com\<Rightarrow>Mat\<Rightarrow>bool"where
"svalid P S Q=(\<forall>\<rho> p. positive \<rho>\<longrightarrow>denofun S \<rho> p\<longrightarrow>Tr (mat_mult (mat_sub I Q) p)\<le>Tr (mat_mult (mat_sub I P) \<rho>))"
lemma eq_valid:"svalid P S Q\<Longrightarrow>valid P S Q"
using Ident mult_sub_allo1 svalid_def tr_allo1 valid_def by fastforce
lemma eq_valids:"valid P S Q\<Longrightarrow>svalid P S Q"
apply(simp add:valid_def)
apply(simp add:svalid_def)
using Ident mult_sub_allo1 tr_allo1 by fastforce
lemma temp:"Tr (sum m f \<rho> ) =Tr  (mat_mult \<rho> (sum_2 m  f) ) "
apply(induct m)
apply auto
apply (metis Ident exchange)
by (metis exchange mult_allo2 mult_exchange tr_allo)
lemma m_init:"sum_1 m  f=I\<Longrightarrow>sum_2 m  f=I\<Longrightarrow>Tr (sum m f \<rho> ) =Tr \<rho>"
apply(simp add:temp)
apply(subgoal_tac " Tr (mat_mult \<rho> I) = Tr (mat_mult I \<rho> ) ")
apply(simp add:Ident)
apply(simp add:exchange)
done
lemma Initfact: "positive \<rho> \<Longrightarrow> Tr (mat_mult (sum_t m f P ) \<rho>) = Tr (mat_mult P (sum m f \<rho> ))"
apply (induct m,auto)
apply(simp add:mult_allo1)
apply(simp add:mult_allo2)
apply(simp add:tr_allo)
by (metis exchange_tr mult_exchange)
lemma init_rho: "positive a \<Longrightarrow> positive (sum list f a)"
apply(induct list,auto)
by (metis a1 less3 less6 rho_zero zero_add)
lemma a:" \<forall>a p. positive a \<longrightarrow> denofun SKIP a p \<longrightarrow> positive p"
apply auto
done
lemma b:" \<forall>a p. positive a \<longrightarrow> denofun (Init x1 x2) a p \<longrightarrow> positive p"
apply auto
apply(rule init_rho,auto)
done
lemma d:" \<forall>a p. positive a \<longrightarrow> denofun (Cond []) a p \<longrightarrow> positive p"
apply auto
using a1 less11 by auto
lemma c:" (\<And>a aa b ab ba xaaa.
               (a, aa, b) \<in> set x \<Longrightarrow>
               (ab, ba) \<in> Basic_BNFs.snds (a, aa, b) \<Longrightarrow>
               xaaa \<in> Basic_BNFs.fsts (ab, ba) \<Longrightarrow> \<forall>a. positive a \<longrightarrow> (\<forall>p. denofun xaaa a p \<longrightarrow> positive p)) \<Longrightarrow>
           positive a \<Longrightarrow> \<forall>aa b c. (aa, b, c) \<in> set x \<longrightarrow> denofun b (u aa a) c \<Longrightarrow> positive (accum x)"
apply(induct x,auto)
apply (simp add: a1 less11)
by (metis (no_types, hide_lams) c1 empty_iff fst_eqD fsts.simps insert_iff less3_aux mult_exchange prod_set_simps(1) prod_set_simps(2) snd_eqD snds.simps u_def)

lemma e: assumes  "denofun (While x1 x2 c x4) a p"
     shows "\<forall>s s'. positive s\<longrightarrow>denofun c s s'\<longrightarrow>positive s'\<Longrightarrow>positive a\<Longrightarrow> positive p"
 using assms
 apply(induct "While x1 x2 c x4" a p)
 apply auto
by (metis c1 less3_aux u_def)
lemma positive_deno:"\<forall>a p. positive a\<longrightarrow>denofun s a p\<longrightarrow>positive p"
apply(induct s)
apply(simp add:a)
apply(simp add:b)
using less3_aux apply auto[1]
apply blast
prefer 2
using quantum_hoare_logic.e apply blast
apply auto
apply(simp add:c)
done
primrec sum1::"(Mat*com*Mat) list\<Rightarrow>Mat"where
"sum1 []  =zero"|
"sum1  (a#M)  =  (mat_add (uu (fst a ) (snd (snd a)))  (sum1 M  ))  "
primrec validlist :: "(Mat * com * Mat) list \<Rightarrow> Mat \<Rightarrow> bool" where
"validlist [] Q = True "
| "validlist (a # mcml) Q = ( (valid (snd (snd a)) (fst (snd a)) Q) \<and> (validlist  mcml Q) )"
definition matsum::"nat\<Rightarrow>nat\<Rightarrow>Mat\<Rightarrow>Mat" where
"matsum m n P=(sum_t (h m) f P )"
definition matUtrans::"Mat\<Rightarrow>nat\<Rightarrow>Mat\<Rightarrow>Mat"where
"matUtrans U n P =(mat_mult (mat_mult (dag U) P) U)"
(*six rules*)
lemma Skip:"valid P SKIP P"
apply(simp add:valid_def)
apply auto
done
lemma Utrans:"wellDefined (Utrans U n) \<Longrightarrow>valid  (matUtrans U n P)  (Utrans U n) P"
apply(simp add:valid_def matUtrans_def)
apply auto
by (smt Ident UMat_def exchange_tr mult_exchange)
lemma Init:"wellDefined (Init m n) \<Longrightarrow>valid (matsum m n P) (Init m n) P"
apply(simp add:valid_def matsum_def)
apply auto
apply(simp add:m_init)
apply(simp add:Initfact)
done
lemma Seq:"valid P s1 Q\<Longrightarrow>valid Q s2 R\<Longrightarrow>valid P (s1;s2) R"
apply(simp add:valid_def,auto)
apply(drule_tac x="\<rho>" in spec)
apply(subgoal_tac " positive \<rho>\<Longrightarrow>denofun s1 \<rho> p''\<Longrightarrow>positive p''")
apply(drule_tac x="p''" in spec)
apply auto
apply force
apply(simp add:positive_deno)
done
lemma Measure_aux:"wellDefined (Cond M) \<Longrightarrow>
\<forall>\<rho> p. positive \<rho> \<longrightarrow> denofun (Cond M) \<rho> p \<longrightarrow> Tr (mat_mult (sum1 M) \<rho>) \<le> Tr (mat_mult Q p) +Tr (mat_mult (M_sum M) \<rho>) - Tr p \<Longrightarrow>
\<forall>\<rho> p. positive \<rho> \<longrightarrow> denofun (Cond M) \<rho> p \<longrightarrow> Tr (mat_mult (sum1 M) \<rho>) \<le> Tr (mat_mult Q p) + Tr \<rho> - Tr p"
by (simp add: Ident)
lemma Measure_aux2:" validlist M Q \<Longrightarrow>
    \<forall>\<rho> p. positive \<rho> \<longrightarrow> denofun (Cond M) \<rho> p \<longrightarrow> Tr (mat_mult (sum1 M) \<rho>) \<le> Tr (mat_mult Q p) + Tr (mat_mult (M_sum M) \<rho>) - Tr p"
apply(induct M,auto)
apply (simp add: zero_mult_r)
apply(drule_tac x="\<rho>"in spec)
apply auto
by (smt denofun.intros(5) exchange_tr less3_aux mult_allo1 mult_exchange tr_allo u_def uu_def valid_def)
lemma Measure:"wellDefined (Cond M) \<Longrightarrow> validlist M Q \<Longrightarrow> valid (sum1 M) (Cond M ) Q"
unfolding valid_def
apply(rule Measure_aux)
apply (simp)
apply(rule Measure_aux2,auto)
done
lemma While_aux:assumes "denofun (While m0 m1 S Q) \<rho> p " and" \<forall>\<rho>. positive \<rho> \<longrightarrow>
               (\<forall>p. denofun S \<rho> p \<longrightarrow> Tr (mat_mult (mat_sub I (mat_add (uu m0 P) (uu m1 Q))) p) \<le> Tr (mat_mult (mat_sub I Q) \<rho>))"and
               " mat_add (mat_mult (dag m0) m0) (mat_mult (dag m1) m1) = I"and" wellDefined S"
               and " positive \<rho>"
shows "  Tr (mat_mult (mat_sub I P) p) \<le> Tr (mat_mult (mat_sub I (mat_add (uu m0 P) (uu m1 Q))) \<rho>)"
           using assms
           apply(induct "While m0 m1 S Q" \<rho> p)
           apply auto
           apply(simp add:mult_allo2)
           apply(simp add:tr_allo)
           apply(subgoal_tac "positive p''")
           prefer 2
           apply (metis less3_aux positive_deno u_def)
           apply auto
           apply(subgoal_tac " Tr (mat_mult (mat_sub I P) (u m0 p)) +  Tr (mat_mult (mat_sub I (mat_add (uu m0 P) (uu m1 Q))) p'')
                 \<le> Tr (mat_mult (mat_sub I (mat_add (uu m0 P) (uu m1 Q))) p)")
           apply auto
           apply(subgoal_tac " Tr (mat_mult (mat_sub I (mat_add (uu m0 P) (uu m1 Q))) p'') \<le> Tr (mat_mult (mat_sub I Q) (u m1 p))")
           prefer 2
           apply (simp add: less3_aux u_def)
           apply(subgoal_tac "positive (u m1 p)")
           prefer 2
           apply (simp add: less3_aux u_def)
           apply auto
           apply(subgoal_tac " Tr (mat_mult (mat_sub I (mat_add (uu m0 P) (uu m1 Q))) p'') \<le> Tr (mat_mult (mat_sub I Q) (u m1 p))")
           prefer 2
           apply blast
           apply(subgoal_tac " Tr (mat_mult (mat_sub I P) (u m0 p)) + Tr (mat_mult (mat_sub I Q) (u m1 p))
                 \<le> Tr (mat_mult (mat_sub I (mat_add (uu m0 P) (uu m1 Q))) p)")
           apply linarith
           apply(simp add:mult_sub_allo1)
           apply(simp add:Ident)
           apply(simp add:tr_allo1)
           apply(subgoal_tac "Tr (u m0 p)+Tr (u m1 p) =Tr p")
           prefer 2
           apply(simp add:u_def)
           apply(simp add:exchange_tr)
           apply (metis Ident mult_allo1 mult_exchange tr_allo) 
           apply(subgoal_tac " Tr p  - Tr (mat_mult P (u m0 p)) -  Tr (mat_mult Q (u m1 p))
                  \<le> Tr p - Tr (mat_mult (mat_add (uu m0 P) (uu m1 Q)) p) ")
           apply auto
           apply(subgoal_tac " Tr (mat_mult P (u m0 p))+ Tr (mat_mult Q (u m1 p)) =Tr (mat_mult (mat_add (uu m0 P) (uu m1 Q)) p)")
           apply auto
           apply(simp add:uu_def)
           apply(simp add:u_def)
           by (smt exchange_tr mult_allo1 mult_exchange tr_allo)
lemma While1:"wellDefined (While m0 m1 S Q) \<Longrightarrow> 
          svalid Q S (mat_add (uu m0 P) (uu m1 Q)) \<Longrightarrow>valid (mat_add (uu m0 P) (uu m1 Q))  (While m0 m1 S Q ) P"
apply(rule eq_valid)
apply(simp add:svalid_def,auto)
by (simp add: While_aux)
lemma While:"wellDefined (While m0 m1 S Q) \<Longrightarrow> 
          valid Q S (mat_add (uu m0 P) (uu m1 Q)) \<Longrightarrow>valid (mat_add (uu m0 P) (uu m1 Q))  (While m0 m1 S Q ) P"
apply(rule While1,auto)
by (simp add: eq_valids)
lemma order:"less P Pa\<Longrightarrow>valid Pa S Q\<Longrightarrow>valid P S Q"
apply(simp add:valid_def)
apply auto
using less2 by fastforce
lemma Order:"less P Pa\<Longrightarrow>valid Pa S Qa\<Longrightarrow>less Qa Q\<Longrightarrow>valid P S Q"
apply(simp add:valid_def,auto)
by (smt less2 positive_deno)
(*  about wlp     *)
function wlp::"Mat\<Rightarrow>com\<Rightarrow>Mat" where
"wlp P (SKIP) =P"|
"wlp P (Init m n) =matsum m n P"|
"wlp P (Utrans U n) =matUtrans U n P"|
"wlp P ( Seq c1 c2) =wlp (wlp P c2) c1"|
"wlp P (Cond mcl ) = (case mcl of [] \<Rightarrow> zero
  | mc # mcr \<Rightarrow> mat_add (uu (fst mc) (wlp P (fst (snd mc))))  (wlp P (Cond mcr)) ) " |
"wlp P (While m0 m1 s  Q ) = zero"
by  pat_completeness auto 
termination 
 apply (relation "measure (\<lambda>(c,m).rank m)", auto )
done

lemma while_deno_tr:assumes " denofun (While x1 x2 s x4) p p'" and" mat_add (mat_mult (dag x1) x1) (mat_mult (dag x2) x2) = I "
and "wellDefined s"and "\<forall>p. positive p \<longrightarrow> (\<forall>p'. denofun s p p' \<longrightarrow> Tr p' \<le> Tr p)"and " positive p"
shows "Tr p' \<le> Tr p"
using assms
apply(induct "While x1 x2 s x4" p p')
apply auto
apply(subgoal_tac "positive (u x2 p)")
prefer 2
apply (simp add: less3_aux u_def)
apply(subgoal_tac "Tr p''\<le>Tr (u x2 p)")
prefer 2
apply simp
apply(subgoal_tac "Tr p'\<le>Tr (u x2 p)")
prefer 2
apply (smt positive_deno)
apply(simp add:tr_allo)
apply(subgoal_tac "Tr (u x1 p) + Tr (u x2 p) \<le> Tr p ")
prefer 2
apply auto
apply(simp add:u_def)
apply(simp add:exchange_tr)
apply(subgoal_tac "  Tr (mat_mult (mat_mult (dag x1) x1) p) + Tr (mat_mult (mat_mult (dag x2)  x2) p) \<le> Tr p ")
apply(simp add:mult_exchange)
apply(subgoal_tac "Tr (mat_add (mat_mult (mat_mult (dag x1) x1) p) (mat_mult (mat_mult (dag x2) x2) p)  ) \<le>Tr p")
apply(simp add:tr_allo)
apply(subgoal_tac "Tr (mat_mult (mat_add (mat_mult (dag x1) x1) (mat_mult (dag x2) x2 )) p) \<le>Tr p")
apply (metis mult_allo1)
apply (simp add:Ident)
done
lemma cond_deno_tr:  " (\<And>a aa b. (a, aa, b) \<in> set x \<Longrightarrow>\<forall>p. positive p \<longrightarrow> (\<forall>p'. denofun aa p p' \<longrightarrow> Tr p' \<le> Tr p)) \<Longrightarrow>
           \<forall>a aa b. (a, aa, b) \<in> set x \<longrightarrow> wellDefined aa \<Longrightarrow>
           positive p \<Longrightarrow> \<forall>a b c. (a, b, c) \<in> set x \<longrightarrow> denofun b (u a p) c \<Longrightarrow> Tr (accum x) \<le> Tr (mat_mult (M_sum x) p)"
           apply(induct x,auto)
           using zero_mult_l apply auto[1]
           apply(simp add:tr_allo)
           apply(simp add:mult_allo1)
           apply(simp add:tr_allo)
           by (metis (no_types, hide_lams) add_mono exchange_tr less3_aux mult_exchange u_def)
(*Tr [S](\<rho>) \<le>Tr \<rho>*)
lemma deno_tr:"wellDefined s\<Longrightarrow>\<forall>p p'. positive p\<longrightarrow> denofun s p p'\<longrightarrow>Tr p' \<le>Tr p"
apply(induct s)
apply auto
apply (simp add: m_init)
apply (smt Ident UMat_def exchange_tr mult_exchange)
using positive_deno apply force
prefer 2
apply (simp add: while_deno_tr)
apply(subgoal_tac " Tr (accum x) \<le> Tr (mat_mult (M_sum x) p)")
apply(simp add:Ident)
apply(rule cond_deno_tr, auto)
using fsts.intros snds.intros apply fastforce
using fsts.intros snds.intros by fastforce
lemma temp_wlp:" positive P \<Longrightarrow> positive (sum_t a f P)"
apply(induct a,auto)
by (metis c1 dag_dag less3_aux)
lemma temp_wlp1:" ((\<And>a aa b. (a, aa, b) \<in> set x \<Longrightarrow> \<forall>P. positive P \<longrightarrow> positive (wlp P aa)) \<Longrightarrow>
        positive (case x of [] \<Rightarrow> zero | mc # mcr \<Rightarrow> mat_add (uu (fst mc) (wlp P (fst (snd mc)))) (wlp P (Cond mcr)))) \<Longrightarrow>
       (\<And>aaa aaaa ba. aaa = a \<and> aaaa = aa \<and> ba = b \<or> (aaa, aaaa, ba) \<in> set x \<Longrightarrow> \<forall>P. positive P \<longrightarrow> positive (wlp P aaaa)) \<Longrightarrow>
       positive P \<Longrightarrow> positive
       (mat_add (uu a (wlp P aa)) (case x of [] \<Rightarrow> zero | mc # mcr \<Rightarrow> mat_add (uu (fst mc) (wlp P (fst (snd mc)))) (wlp P (Cond mcr))))"
apply(subgoal_tac "positive (wlp P aa)")
prefer 2
apply blast
apply(subgoal_tac "positive (uu a (wlp P aa)) ")
prefer 2
apply(simp add:uu_def)
apply (metis dag_dag less3_aux)
using c1 by blast
 lemma temp_wlp2:" (\<And>a aa b. (a, aa, b) \<in> set x \<Longrightarrow> \<forall>P. positive P \<longrightarrow> positive (wlp P aa)) \<Longrightarrow>
    positive P \<Longrightarrow> positive (case x of [] \<Rightarrow> zero | mc # mcr \<Rightarrow> mat_add (uu (fst mc) (wlp P (fst (snd mc)))) (wlp P (Cond mcr)))"
apply(induct x,auto)
using a1 less11 apply blast
apply( rule temp_wlp1,auto)
done
(*positive wlp P S*)
lemma positive_wlp: "\<forall>P. positive P\<longrightarrow>positive (wlp P S)"
apply(induct S,auto)
apply(simp add:matsum_def temp_wlp)
apply (metis dag_dag less3_aux matUtrans_def)
prefer 2
apply (simp add: a1 less11)
apply(rule temp_wlp2,auto)
using fsts.intros snds.intros by fastforce
(*while_wlp*)
lemma while_wlp_aux:assumes" denofun (While m1 m2 com Q) \<rho> p"and"mat_add (mat_mult (dag m1) m1) (mat_mult (dag m2) m2) = I"and
" wellDefined com" and " positive \<rho> "and "positive P"
shows " Tr (mat_mult (mat_sub I P) p) \<le> Tr \<rho>"
using assms
apply(induct "While m1 m2 com Q" \<rho> p)
apply auto
apply(subgoal_tac "positive p''")
prefer 2
apply (metis less3_aux positive_deno u_def)
apply auto
apply(simp add:mult_allo2)
apply(simp add:tr_allo)
apply(simp add:mult_sub_allo1)
apply(simp add:Ident tr_allo1)
apply(subgoal_tac "Tr (u m1 p) - Tr (mat_mult P (u m1 p)) + Tr p'' \<le> Tr p ")
apply auto
apply(subgoal_tac "Tr p''\<le>Tr (u m2 p)")
prefer 2
apply (simp add: deno_tr less3_aux u_def)
apply(subgoal_tac " Tr (u m1 p) - Tr (mat_mult P (u m1 p)) + Tr (u m2 p) \<le> Tr p ")
apply auto
by (smt Ident exchange_tr less3_aux less44 mult_allo1 mult_exchange tr_allo u_def)
(*wlp-while*)
lemma while_wlp:"positive P\<Longrightarrow>wellDefined (While m1 m2 com Q) \<Longrightarrow>valid (wlp P (While m1 m2 com Q)) (While m1 m2 com Q) P"
apply(rule eq_valid)
apply(simp add:svalid_def,auto)
apply(simp add:zero_sub)
apply(simp add:Ident)
apply(simp add:while_wlp_aux)
done
lemma skip_wlp:"valid (wlp P SKIP) SKIP P"
apply (simp add:valid_def)
apply auto
done
lemma init_wlp:"wellDefined (Init m n) \<Longrightarrow>valid (wlp P (Init m n)) (Init m n) P"
using Init valid_def by auto
lemma utrans_wlp:"wellDefined (Utrans U n) \<Longrightarrow>valid (wlp P (Utrans U n)) (Utrans U n) P"
using Utrans valid_def by auto
lemma seq_wlp:"       \<forall>Q. positive Q \<longrightarrow> valid (wlp Q S1) S1 Q \<Longrightarrow>
       \<forall>Q. positive Q \<longrightarrow> valid (wlp Q S2) S2 Q \<Longrightarrow>
       wellDefined S1 \<Longrightarrow> wellDefined S2 \<Longrightarrow> positive Q \<Longrightarrow> valid (wlp (wlp Q S2) S1) (S1; S2) Q"
apply(simp add:valid_def)
apply auto
apply(subgoal_tac "positive (wlp Q S2)")
apply(drule_tac x="(wlp Q S2)"in spec)
apply(drule_tac x="Q"in spec)
apply auto
apply(drule_tac x="\<rho>"in spec)
apply(subgoal_tac "positive p''")
apply(drule_tac x="p''"in spec)
apply auto
apply(drule_tac x="p''"in spec)
apply auto
apply(drule_tac x="p"in spec)
using positive_deno apply blast
apply(simp add:positive_wlp)
done

lemma b1:" (\<And>\<rho>. (\<And>a aa b. (a, aa, b) \<in> set x \<Longrightarrow>
                       \<forall>Q. positive Q \<longrightarrow>
                           (\<forall>\<rho>. positive \<rho> \<longrightarrow> (\<forall>p. denofun aa \<rho> p \<longrightarrow> Tr (mat_mult (wlp Q aa) \<rho>) \<le> Tr (mat_mult Q p) + Tr \<rho> - Tr p))) \<Longrightarrow>
             \<forall>a aa. (\<exists>b. (a, aa, b) \<in> set x) \<longrightarrow> wellDefined aa \<Longrightarrow>
             positive \<rho> \<Longrightarrow>
             \<forall>a b c. (a, b, c) \<in> set x \<longrightarrow> denofun b (u a \<rho>) c \<Longrightarrow>
             Tr (mat_mult (case x of [] \<Rightarrow> zero | mc # mcr \<Rightarrow> mat_add (uu (fst mc) (wlp Q (fst (snd mc)))) (wlp Q (Cond mcr))) \<rho>)
             \<le> Tr (mat_mult Q (accum x)) + Tr (mat_mult (M_sum x) \<rho>) - Tr (accum x)) \<Longrightarrow>
       (\<And>aaa aaaa ba.
           aaa = a \<and> aaaa = aa \<and> ba = b \<or> (aaa, aaaa, ba) \<in> set x \<Longrightarrow>
           \<forall>Q. positive Q \<longrightarrow>
               (\<forall>\<rho>. positive \<rho> \<longrightarrow> (\<forall>p. denofun aaaa \<rho> p \<longrightarrow> Tr (mat_mult (wlp Q aaaa) \<rho>) \<le> Tr (mat_mult Q p) + Tr \<rho> - Tr p))) \<Longrightarrow>
       \<forall>aaa aaaa. (\<exists>ba. aaa = a \<and> aaaa = aa \<and> ba = b \<or> (aaa, aaaa, ba) \<in> set x) \<longrightarrow> wellDefined aaaa \<Longrightarrow>
        \<forall>aaa ba c. (aaa = a \<and> ba = aa \<and> c = b \<longrightarrow> denofun aa (u a \<rho>) b) \<and> ((aaa, ba, c) \<in> set x \<longrightarrow> denofun ba (u aaa \<rho>) c) \<Longrightarrow>
        positive \<rho> \<Longrightarrow>
             Tr (mat_mult (case x of [] \<Rightarrow> zero | mc # mcr \<Rightarrow> mat_add (uu (fst mc) (wlp Q (fst (snd mc)))) (wlp Q (Cond mcr))) \<rho>)
             \<le> Tr (mat_mult Q (accum x)) + Tr (mat_mult (M_sum x) \<rho>) - Tr (accum x)
               "
by fastforce
lemma b2:"           Tr (mat_mult (case x of [] \<Rightarrow> zero | mc # mcr \<Rightarrow> mat_add (uu (fst mc) (wlp Q (fst (snd mc)))) (wlp Q (Cond mcr))) \<rho>)
             \<le> Tr (mat_mult Q (accum x)) + Tr (mat_mult (M_sum x) \<rho>) - Tr (accum x) \<Longrightarrow>
       (\<And>aaa aaaa ba.
           aaa = a \<and> aaaa = aa \<and> ba = b \<or> (aaa, aaaa, ba) \<in> set x \<Longrightarrow>
           \<forall>Q. positive Q \<longrightarrow>
               (\<forall>\<rho>. positive \<rho> \<longrightarrow> (\<forall>p. denofun aaaa \<rho> p \<longrightarrow> Tr (mat_mult (wlp Q aaaa) \<rho>) \<le> Tr (mat_mult Q p) + Tr \<rho> - Tr p))) \<Longrightarrow>
       \<forall>aaa aaaa. (\<exists>ba. aaa = a \<and> aaaa = aa \<and> ba = b \<or> (aaa, aaaa, ba) \<in> set x) \<longrightarrow> wellDefined aaaa \<Longrightarrow>
       positive Q \<Longrightarrow>
       positive \<rho> \<Longrightarrow>
       \<forall>aaa ba c. (aaa = a \<and> ba = aa \<and> c = b \<longrightarrow> denofun aa (u a \<rho>) b) \<and> ((aaa, ba, c) \<in> set x \<longrightarrow> denofun ba (u aaa \<rho>) c) \<Longrightarrow>
       Tr (mat_mult (uu a (wlp Q aa)) \<rho>) +
       Tr (mat_mult (case x of [] \<Rightarrow> zero | mc # mcr \<Rightarrow> mat_add (uu (fst mc) (wlp Q (fst (snd mc)))) (wlp Q (Cond mcr))) \<rho>)
       \<le> Tr (mat_mult Q b) + Tr (mat_mult Q (accum x)) + (Tr (mat_mult (mat_mult (dag a) a) \<rho>) + Tr (mat_mult (M_sum x) \<rho>)) -
          (Tr b + Tr (accum x))"
           apply(drule_tac x="a"in spec,auto)
            apply(drule_tac x="a"in spec,auto)
             apply(drule_tac x="aa"in spec,auto)
              apply(drule_tac x="aa"in spec)
               apply(drule_tac x="b"in spec,auto)
apply (smt exchange_tr less3_aux mult_exchange u_def uu_def)
apply(subgoal_tac " (\<forall>\<rho>. positive \<rho> \<longrightarrow> (\<forall>p. denofun aa \<rho> p \<longrightarrow> Tr (mat_mult (wlp Q aa) \<rho>) \<le> Tr (mat_mult Q p) + Tr \<rho> - Tr p))")
prefer 2
apply blast
 apply(drule_tac x="u a \<rho>"in spec)
 apply(subgoal_tac "positive (u a \<rho>)")
 prefer 2
apply (simp add: less3_aux u_def)
apply auto
 apply(drule_tac x="b"in spec,auto)
by (smt exchange_tr mult_exchange u_def uu_def)

lemma a1:"(\<And>a aa b . (a, aa, b) \<in> set x \<Longrightarrow>
               \<forall>Q. positive Q \<longrightarrow>
                   (\<forall>\<rho>. positive \<rho> \<longrightarrow> (\<forall>p. denofun aa \<rho> p \<longrightarrow> Tr (mat_mult (wlp Q aa) \<rho>) \<le> Tr (mat_mult Q p) + Tr \<rho> - Tr p))) \<Longrightarrow>
           \<forall>a aa b. (a, aa, b) \<in> set x \<longrightarrow> wellDefined aa \<Longrightarrow>
           positive Q \<Longrightarrow>
           \<forall>\<rho>. positive \<rho> \<longrightarrow>
               (\<forall>p. denofun (Cond x) \<rho> p \<longrightarrow>
                    Tr (mat_mult (case x of [] \<Rightarrow> zero | mc # mcr \<Rightarrow> mat_add (uu (fst mc) (wlp Q (fst (snd mc)))) (wlp Q (Cond mcr))) \<rho>)
                    \<le> Tr (mat_mult Q p) + Tr (mat_mult (M_sum x) \<rho>) - Tr p)"
apply(auto)
apply(induct x,auto)
apply (simp add: zero_mult_r)
      apply(simp add:mult_allo1)
      apply(simp add:tr_allo)
      apply(simp add:mult_allo2)
      apply(simp add:tr_allo)
      apply(rule b2,auto)
      apply(rule b1,auto)
      done
 lemma a2:" (\<And>a aa b aaa ba xaaa.
               (a, aa, b) \<in> set x \<Longrightarrow>
               (aaa, ba) \<in> Basic_BNFs.snds (a, aa, b) \<Longrightarrow>
               xaaa \<in> Basic_BNFs.fsts (aaa, ba) \<Longrightarrow>
               \<forall>Q. positive Q \<longrightarrow>
                   (\<forall>\<rho>. positive \<rho> \<longrightarrow> (\<forall>p. denofun xaaa \<rho> p \<longrightarrow> Tr (mat_mult (wlp Q xaaa) \<rho>) \<le> Tr (mat_mult Q p) + Tr \<rho> - Tr p))) \<Longrightarrow>
           \<forall>a aa b. (a, aa, b) \<in> set x \<longrightarrow>
                    (\<forall>aaa ba. (aaa, ba) \<in> Basic_BNFs.snds (a, aa, b) \<longrightarrow>
                              (\<forall>xaaa. xaaa \<in> Basic_BNFs.fsts (aaa, ba) \<longrightarrow> wellDefined xaaa)) \<Longrightarrow>
           positive Q \<Longrightarrow>
           \<forall>\<rho>. positive \<rho> \<longrightarrow>
               (\<forall>p. denofun (Cond x) \<rho> p \<longrightarrow>
                    Tr (mat_mult (case x of [] \<Rightarrow> zero | mc # mcr \<Rightarrow> mat_add (uu (fst mc) (wlp Q (fst (snd mc)))) (wlp Q (Cond mcr))) \<rho>)
                    \<le> Tr (mat_mult Q p) + Tr (mat_mult (M_sum x) \<rho>) - Tr p)"
apply(rule a1,auto)
using fsts.intros snds.intros apply fastforce+
done
lemma cond_wlp_aux:" (\<And>a aa b aaa ba xaaa.
               (a, aa, b) \<in> set x \<Longrightarrow>
               (aaa, ba) \<in> Basic_BNFs.snds (a, aa, b) \<Longrightarrow>
               xaaa \<in> Basic_BNFs.fsts (aaa, ba) \<Longrightarrow>
               \<forall>Q. positive Q \<longrightarrow>
                   (\<forall>\<rho>. positive \<rho> \<longrightarrow> (\<forall>p. denofun xaaa \<rho> p \<longrightarrow> Tr (mat_mult (wlp Q xaaa) \<rho>) \<le> Tr (mat_mult Q p) + Tr \<rho> - Tr p))) \<Longrightarrow>
           \<forall>a aa b. (a, aa, b) \<in> set x \<longrightarrow>
                    (\<forall>aaa ba. (aaa, ba) \<in> Basic_BNFs.snds (a, aa, b) \<longrightarrow>
                              (\<forall>xaaa. xaaa \<in> Basic_BNFs.fsts (aaa, ba) \<longrightarrow> wellDefined xaaa)) \<Longrightarrow>
            M_sum x = I \<Longrightarrow>
           positive Q \<Longrightarrow>
           \<forall>\<rho>. positive \<rho> \<longrightarrow>
               (\<forall>p. denofun (Cond x) \<rho> p \<longrightarrow>
                    Tr (mat_mult (case x of [] \<Rightarrow> zero | mc # mcr \<Rightarrow> mat_add (uu (fst mc) (wlp Q (fst (snd mc)))) (wlp Q (Cond mcr))) \<rho>)
                    \<le> Tr (mat_mult Q p) + Tr (mat_mult (M_sum x) \<rho>) - Tr p)"
apply(rule a2,auto)
done
lemma cond_wlp:" (\<And>a aa b aaa ba xaaa.
               (a, aa, b) \<in> set x \<Longrightarrow>
               (aaa, ba) \<in> Basic_BNFs.snds (a, aa, b) \<Longrightarrow>
               xaaa \<in> Basic_BNFs.fsts (aaa, ba) \<Longrightarrow>
               \<forall>Q. positive Q \<longrightarrow>
                   (\<forall>\<rho>. positive \<rho> \<longrightarrow> (\<forall>p. denofun xaaa \<rho> p \<longrightarrow> Tr (mat_mult (wlp Q xaaa) \<rho>) \<le> Tr (mat_mult Q p) + Tr \<rho> - Tr p))) \<Longrightarrow>
           \<forall>a aa b. (a, aa, b) \<in> set x \<longrightarrow>
                    (\<forall>aaa ba. (aaa, ba) \<in> Basic_BNFs.snds (a, aa, b) \<longrightarrow>
                              (\<forall>xaaa. xaaa \<in> Basic_BNFs.fsts (aaa, ba) \<longrightarrow> wellDefined xaaa)) \<Longrightarrow>
            M_sum x = I \<Longrightarrow>
           positive Q \<Longrightarrow>
           \<forall>\<rho>. positive \<rho> \<longrightarrow>
               (\<forall>p. denofun (Cond x) \<rho> p \<longrightarrow>
                    Tr (mat_mult (case x of [] \<Rightarrow> zero | mc # mcr \<Rightarrow> mat_add (uu (fst mc) (wlp Q (fst (snd mc)))) (wlp Q (Cond mcr))) \<rho>)
                    \<le> Tr (mat_mult Q p) + Tr \<rho> - Tr p)"
            apply(subgoal_tac "           \<forall>\<rho>. positive \<rho> \<longrightarrow>
               (\<forall>p. denofun (Cond x) \<rho> p \<longrightarrow>
                    Tr (mat_mult (case x of [] \<Rightarrow> zero | mc # mcr \<Rightarrow> mat_add (uu (fst mc) (wlp Q (fst (snd mc)))) (wlp Q (Cond mcr))) \<rho>)
                    \<le> Tr (mat_mult Q p) + Tr (mat_mult (M_sum x) \<rho>) - Tr p)")
            apply(simp add:Ident)
            apply(rule cond_wlp_aux ,auto)
            done
lemma soundwp:"wellDefined S\<Longrightarrow>\<forall>Q. positive Q\<longrightarrow>valid (wlp Q S) S Q"
apply(induct S)
prefer 6
using while_wlp apply blast
apply (simp add: Skip)
apply (simp add: Init)
apply (simp add: Utrans)
apply auto
apply (simp add: seq_wlp)
apply(simp add:valid_def)
apply(rule cond_wlp,auto)
done
lemma WLPsound:"positive Q\<Longrightarrow>wellDefined S\<Longrightarrow>valid (wlp Q S) S Q"
apply(simp add: soundwp)
done
lemma ord_wlp:"positive Q\<Longrightarrow>wellDefined S\<Longrightarrow>less P (wlp Q S)\<Longrightarrow>valid P S Q"
apply(rule_tac Pa="wlp Q S" in order,auto)
apply(rule WLPsound)
apply auto
done


declare uu_def[simp] zero_add[simp]
ML_file "Quantum_Hoare_tac.ML"
method_setup vcg = {*
  Scan.succeed (fn ctxt => SIMPLE_METHOD' (quantum_hoare_tac ctxt (K all_tac))) *}
method_setup vcg_simp = {*
  Scan.succeed (fn ctxt =>
    SIMPLE_METHOD' (quantum_hoare_tac ctxt (asm_full_simp_tac ctxt))) *}





end
