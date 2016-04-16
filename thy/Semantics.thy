(*formal semantics of brainfuck*)

theory Semantics
imports Verifuck
begin


datatype 'a outp = Output "'a list"
datatype 'a inp = Input "'a list"
datatype 'a state = Error | Normal "'a tape" "'a inp" "'a outp"


inductive eval_bf :: "instr list \<Rightarrow> 'a::{zero,one,plus,minus} state \<Rightarrow> 'a state \<Rightarrow> bool"  where
init:  "s = s' \<Longrightarrow> eval_bf [] s s'" |
       "eval_bf [Right] (Normal (Tape lt c []) inp outp)       (Normal (Tape (c#lt) 0 []) inp outp)" |
       "eval_bf [Right] (Normal (Tape lt c (rt#rts)) inp outp) (Normal (Tape (c#lt) rt rts) inp outp)" |
       "eval_bf [Left]  (Normal (Tape [] c rt) inp outp)       Error"  |
       "eval_bf [Left]  (Normal (Tape (lt#lts) c rt) inp outp) (Normal (Tape lts lt (c#rt)) inp outp)" |
       "eval_bf [Incr]  (Normal (Tape lt c rt) inp outp)       (Normal (Tape lt (c + 1) rt) inp outp)" |
       "eval_bf [Decr] (Normal (Tape lt c rt) inp outp)       (Normal (Tape lt (c - 1) rt) inp outp)" |
       "eval_bf [Out] (Normal (Tape lt c rt) inp (Output outp))     (Normal (Tape lt c rt) inp (Output (c#outp)))" |
       "eval_bf [In]  (Normal (Tape lt _ rt) (Input []) outp)       (Normal (Tape lt 0 rt) (Input []) outp)" |
       "eval_bf [In]  (Normal (Tape lt _ rt) (Input (i#is)) outp)   (Normal (Tape lt i rt) (Input is) outp)" |
seq:  "eval_bf code s s' \<Longrightarrow> eval_bf code' s' s'' \<Longrightarrow> eval_bf (code@code') s s''" |
whileTrue:      "c \<noteq> 0 \<Longrightarrow> eval_bf code (Normal (Tape lt c rt) inp outp) (Normal (Tape lt'' c'' rt'') inp'' outp'') \<Longrightarrow>
                  eval_bf ([Loop]@code@[Pool])  (Normal (Tape lt'' c'' rt'') inp'' outp') (Normal (Tape lt' c' rt') inp' outp') \<Longrightarrow>
        eval_bf ([Loop]@code@[Pool])  (Normal (Tape lt c rt) inp outp)       (Normal (Tape lt' c' rt') inp' outp')" |
whileFalse:      "c = 0 \<Longrightarrow> 
        eval_bf ([Loop]@code@[Pool])  (Normal (Tape lt c rt) inp outp)       (Normal (Tape lt c rt) inp outp)" 


inductive_cases b_bf_init: "eval_bf [] s s'"
thm b_bf_init
inductive_cases b_bf_while: "eval_bf (Loop # code @ [Pool]) s s'"
thm b_bf_while

lemma subst1: "cmd#code' = [cmd]@code'" by (metis append_Cons append_Nil)

lemma seq': "eval_bf [cmd] s s' \<Longrightarrow> eval_bf code' s' s'' \<Longrightarrow> eval_bf (cmd#code') s s''"
apply(subst subst1)
apply(rule eval_bf.seq)
by(auto)

lemma seq_while_split: "eval_bf ([BF_LOOPSTART]@code@[BF_LOOPEND]) s si \<Longrightarrow> eval_bf (code') si s'
   \<Longrightarrow> eval_bf ([BF_LOOPSTART]@code@[BF_LOOPEND]@code') s s'"
  apply(simp)
  apply(rule eval_bf.seq[of "[BF_LOOPSTART]@code@[BF_LOOPEND]" s si "code'", simplified])
by(auto intro: eval_bf.intros)


lemma "eval_bf [] (Normal (Tape [] 0 []) inp outp) (Normal (Tape [] 0 []) inp outp)"
  by(simp add: eval_bf.intros)

(*the nat annotation is important, otherwise, 0+1=1 may not hold!*)
lemma "eval_bf [Incr, Out] (Normal (Tape [] (0::nat) []) inp (Output [])) (Normal (Tape [] 1 []) inp (Output [1]))"
  apply(rule seq')
  apply(auto intro: eval_bf.intros)
 done


lemma "run_bf [instr.Right] inp = []"
  by(simp add: run_bf_def interp_bf.simps init_table_def init_io_def)

lemma eval_bf_emptyD: "eval_bf [] s s' \<Longrightarrow> s = s'"
proof-
  have "eval_bf prog s s' \<Longrightarrow> prog = [] \<Longrightarrow> s = s'" for prog
    apply(induction rule: eval_bf.induct)
    by(simp_all)
  thus "eval_bf [] s s' \<Longrightarrow> s = s'" by simp
qed



lemma "eval_bf prog (Normal (Tape [] 0 []) (Input inp) (Output outp))  (Normal (Tape lt' c' rt') (Input inp') (Output outp')) \<Longrightarrow>
          (run_bf prog inp) @ outp = outp'"
  apply(induction prog "(Normal (Tape [] 0 []) (Input inp) (Output outp))"  "(Normal (Tape lt' c' rt') (Input inp') (Output outp'))" rule: eval_bf.induct)
  apply(simp_all add: interp_bf.simps run_bf_def empty_tape_def init_table_def init_io_def)
  apply (simp_all add: case_prod_beta)

  (*apply(case_tac code)
  apply(simp_all)
  apply(case_tac code')
  apply(simp_all)
  apply(auto dest: eval_bf_emptyD)[1]
  apply(frule eval_bf_emptyD)
  apply(simp)
  apply(auto)[1]

  apply(case_tac a)
  apply(simp_all)
  apply(simp_all split: instr.split_asm)

  apply(erule b_bf_init)
  apply(simp_all)
  apply(auto intro: eval_bf.intros simp add: interp_bf.simps run_bf_def empty_tape_def init_table_def init_io_def)*)
  

end
