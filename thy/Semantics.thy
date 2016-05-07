(*formal semantics of brainfuck*)

theory Semantics
imports Verifuck
begin


datatype 'a outp = Output "'a list"
datatype 'a inp = Input "'a list"
datatype 'a state = Error | Normal "'a tape" "'a inp" "'a outp"

fun aligned_parenthesis :: "instr list \<Rightarrow> nat \<Rightarrow> bool" where
  "aligned_parenthesis [] 0 = True" |
  "aligned_parenthesis [] _ = False" |
  "aligned_parenthesis (Loop#cs) n = aligned_parenthesis cs (Suc n)" |
  "aligned_parenthesis (Pool#_) 0 = False" |
  "aligned_parenthesis (Pool#cs) (Suc n) = aligned_parenthesis cs n" | 
  "aligned_parenthesis (c#cs) n = aligned_parenthesis cs n"

inductive eval_bf :: "instr list \<Rightarrow> 'a::{zero,one,plus,minus} state \<Rightarrow> 'a state \<Rightarrow> bool"  where
init:  "s = s' \<Longrightarrow> eval_bf [] s s'" |
       "eval_bf [Right] (Normal (Tape lt c []) inp outp)       (Normal (Tape (c#lt) 0 []) inp outp)" |
       "eval_bf [Right] (Normal (Tape lt c (rt#rts)) inp outp) (Normal (Tape (c#lt) rt rts) inp outp)" |
       "eval_bf [Left]  (Normal (Tape [] c rt) inp outp)       Error"  |
       "eval_bf [Left]  (Normal (Tape (lt#lts) c rt) inp outp) (Normal (Tape lts lt (c#rt)) inp outp)" |
       "eval_bf [Incr]  (Normal (Tape lt c rt) inp outp)       (Normal (Tape lt (c + 1) rt) inp outp)" |
       "eval_bf [Decr] (Normal (Tape lt c rt) inp outp)       (Normal (Tape lt (c - 1) rt) inp outp)" |
       "eval_bf [Out] (Normal (Tape lt c rt) inp (Output outp))     (Normal (Tape lt c rt) inp (Output (c#outp)))" |
       "eval_bf [In]  (Normal (Tape lt _ rt) (Input []) outp)       (Normal (Tape lt (0 - 1) rt) (Input []) outp)" | (*really?*)
       "eval_bf [In]  (Normal (Tape lt _ rt) (Input (i#is)) outp)   (Normal (Tape lt i rt) (Input is) outp)" |
seq:  "eval_bf code s s' \<Longrightarrow> eval_bf code' s' s'' \<Longrightarrow> eval_bf (code@code') s s''" |
whileTrue:      "c \<noteq> 0 \<Longrightarrow> eval_bf code (Normal (Tape lt c rt) inp outp) (Normal (Tape lt'' c'' rt'') inp'' outp'') \<Longrightarrow>
                  eval_bf ([Loop]@code@[Pool])  (Normal (Tape lt'' c'' rt'') inp'' outp') (Normal (Tape lt' c' rt') inp' outp') \<Longrightarrow>
        eval_bf ([Loop]@code@[Pool])  (Normal (Tape lt c rt) inp outp)       (Normal (Tape lt' c' rt') inp' outp')" |

(*is this correct? what if not aligned_parenthesis ?*)
whileFalse:      "c = 0 \<Longrightarrow>  aligned_parenthesis code 0 \<Longrightarrow>
        eval_bf ([Loop]@code@[Pool])  (Normal (Tape lt c rt) inp outp)       (Normal (Tape lt c rt) inp outp)" 


lemma skip_loop_forward_aligned: 
  "skip_loop_forward cs rs n = Result ([], rs') \<Longrightarrow> aligned_parenthesis cs (Suc n)"
apply(induction cs arbitrary: n rs)
 apply(simp; fail)
apply(case_tac a)
       apply(simp_all)
apply(case_tac n)
 apply(simp_all)
done


inductive_cases "eval_bf [] s s'"

inductive_cases b_bf_while: "eval_bf (Loop # code @ [Pool]) s s'"
thm b_bf_while


(*inductive_cases for [] is not so good*)
lemma b_bf_init: "eval_bf [] s s' \<Longrightarrow> (s' = s \<Longrightarrow> P) \<Longrightarrow> P"
proof - 
  assume "eval_bf [] s s'" and "s' = s \<Longrightarrow> P"
  have "eval_bf prog s s' \<Longrightarrow> prog = [] \<Longrightarrow> (s' = s \<Longrightarrow> P) \<Longrightarrow> P" for prog
    proof(induction prog s s' rule: eval_bf.induct)
    qed(auto intro: eval_bf.intros)
  thus ?thesis using \<open>eval_bf [] s s'\<close> and \<open>s' = s \<Longrightarrow> P\<close> by simp
qed

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
  by(simp add: run_bf_def interp_bf.simps init_table_def)

lemma eval_bf_emptyD: "eval_bf [] s s' \<Longrightarrow> s = s'"
proof-
  have "eval_bf prog s s' \<Longrightarrow> prog = [] \<Longrightarrow> s = s'" for prog
    apply(induction rule: eval_bf.induct)
    by(simp_all)
  thus "eval_bf [] s s' \<Longrightarrow> s = s'" by simp
qed


(*
(*steps left \<Rightarrow> current program \<Rightarrow> executed instructions \<Rightarrow> skip because we are in a loop? \<Rightarrow> ...*)
fun  bounded_machine :: "nat \<Rightarrow> instr list \<Rightarrow> instr list \<Rightarrow> loop_skipper \<Rightarrow> 
                          ('a::{zero,one,minus,plus}, 'b) machine \<Rightarrow> ('a, 'b) machine" where
"bounded_machine 0 _ _ _ m  = m" | (*TODO: error out-of-instructions*)
"bounded_machine _ [] _ NoSkip m  = m" |
"bounded_machine (Suc n) (Incr#cs) rs NoSkip m = bounded_machine n cs (Incr#rs) NoSkip (apfst (tape_map_cur (\<lambda>x. x + 1)) m)" |
"bounded_machine (Suc n) (Decr#cs) rs NoSkip m = bounded_machine n cs (Decr#rs) NoSkip (apfst (tape_map_cur (\<lambda>x. x - 1)) m)" |
"bounded_machine (Suc n) (Left#cs) rs NoSkip m = bounded_machine n cs (Left#rs) NoSkip (apfst tape_shift_left m)" |
"bounded_machine (Suc n) (Right#cs) rs NoSkip m = bounded_machine n cs (Right#rs) NoSkip (apfst tape_shift_right m)" |
"bounded_machine (Suc n) (In#cs) rs NoSkip m = bounded_machine n cs (In#rs) NoSkip ((\<lambda>(tape, io). let (c, io') = read_io io in (tape_map_cur (\<lambda>_. c) tape, io')) m)" |
"bounded_machine (Suc n) (Out#cs) rs NoSkip m = bounded_machine n cs (Out#rs) NoSkip ((\<lambda>(tape, io). (tape, write_io (cur tape) io)) m)" |
"bounded_machine (Suc n) (Loop#cs) rs NoSkip m = bounded_machine n cs (Loop#rs) (SkipForward 0) m" | (*only if current = 0*)
"bounded_machine (Suc n) (Loop#cs) rs (SkipForward s) m = bounded_machine n cs (Loop#rs) (SkipForward (Suc s)) m" |
"bounded_machine (Suc n) (Pool#cs) rs (SkipForward 0) m = bounded_machine n cs (Pool#rs) NoSkip m" |
"bounded_machine (Suc n) (Pool#cs) rs (SkipForward (Suc s)) m = bounded_machine n cs (Loop#rs) (SkipForward s) m" |
"bounded_machine (Suc n) (c#cs) rs (SkipForward s) m = bounded_machine n cs (c#rs) (SkipForward s) m" |
"bounded_machine (Suc n) [] rs (SkipForward s) m = m" | (*no closing ]*)
"bounded_machine (Suc n) (Pool#cs) rs NoSkip m = bounded_machine n cs (Loop#rs) (SkipBackward 0) m" |
"bounded_machine (Suc n) cs (Loop#rs) (SkipBackward 0) m = bounded_machine n (Loop#cs) rs NoSkip m" |
"bounded_machine (Suc n) cs (Loop#rs) (SkipBackward (Suc s)) m = bounded_machine n (Loop#cs) rs (SkipBackward s) m" |
"bounded_machine (Suc n) cs (Pool#rs) (SkipBackward s) m = bounded_machine n (Pool#cs) rs (SkipBackward (Suc s)) m" |
"bounded_machine (Suc n) cs (c#rs) (SkipBackward s) m = bounded_machine n (c#cs) rs (SkipBackward s) m" |
"bounded_machine (Suc n) cs [] (SkipBackward s) m = m" (*no opening [*)
by pat_completeness auto


datatype loop_skipper = NoSkip | SkipForward nat | SkipBackward nat

(*TODO: error of out-of-instructions*)
(*steps left \<Rightarrow> current program \<Rightarrow> executed instructions \<Rightarrow> skip because we are in a loop? \<Rightarrow> ...*)
fun  bounded_machine :: "nat \<Rightarrow> instr list \<Rightarrow> instr list \<Rightarrow> loop_skipper \<Rightarrow> 
                          ('a::{zero,one,minus,plus}, 'b) machine \<Rightarrow> ('a, 'b) machine" where
"bounded_machine 0 _ _ _ m  = m" | (*TODO: error out-of-instructions*)
"bounded_machine _ [] _ NoSkip m  = m" |
"bounded_machine (Suc n) (Incr#cs) rs NoSkip m = bounded_machine n cs (Incr#rs) NoSkip (apfst (tape_map_cur (\<lambda>x. x + 1)) m)" |
"bounded_machine (Suc n) (Decr#cs) rs NoSkip m = bounded_machine n cs (Decr#rs) NoSkip (apfst (tape_map_cur (\<lambda>x. x - 1)) m)" |
"bounded_machine (Suc n) (Left#cs) rs NoSkip m = bounded_machine n cs (Left#rs) NoSkip (apfst tape_shift_left m)" |
"bounded_machine (Suc n) (Right#cs) rs NoSkip m = bounded_machine n cs (Right#rs) NoSkip (apfst tape_shift_right m)" |
"bounded_machine (Suc n) (In#cs) rs NoSkip m = bounded_machine n cs (In#rs) NoSkip ((\<lambda>(tape, io). let (c, io') = read_io io in (tape_map_cur (\<lambda>_. c) tape, io')) m)" |
"bounded_machine (Suc n) (Out#cs) rs NoSkip m = bounded_machine n cs (Out#rs) NoSkip ((\<lambda>(tape, io). (tape, write_io (cur tape) io)) m)" |
"bounded_machine (Suc n) (Loop#cs) rs NoSkip m = bounded_machine n cs (Loop#rs) (SkipForward 0) m" | (*only if current = 0*)
"bounded_machine (Suc n) (Loop#cs) rs (SkipForward s) m = bounded_machine n cs (Loop#rs) (SkipForward (Suc s)) m" |
"bounded_machine (Suc n) (Pool#cs) rs (SkipForward 0) m = bounded_machine n cs (Pool#rs) NoSkip m" |
"bounded_machine (Suc n) (Pool#cs) rs (SkipForward (Suc s)) m = bounded_machine n cs (Loop#rs) (SkipForward s) m" |
"bounded_machine (Suc n) (c#cs) rs (SkipForward s) m = bounded_machine n cs (c#rs) (SkipForward s) m" |
"bounded_machine (Suc n) [] rs (SkipForward s) m = m" | (*no closing ]*)
"bounded_machine (Suc n) (Pool#cs) rs NoSkip m = bounded_machine n cs (Loop#rs) (SkipBackward 0) m" |
"bounded_machine (Suc n) cs (Loop#rs) (SkipBackward 0) m = bounded_machine n (Loop#cs) rs NoSkip m" |
"bounded_machine (Suc n) cs (Loop#rs) (SkipBackward (Suc s)) m = bounded_machine n (Loop#cs) rs (SkipBackward s) m" |
"bounded_machine (Suc n) cs (Pool#rs) (SkipBackward s) m = bounded_machine n (Pool#cs) rs (SkipBackward (Suc s)) m" |
"bounded_machine (Suc n) cs (c#rs) (SkipBackward s) m = bounded_machine n (c#cs) rs (SkipBackward s) m" |
"bounded_machine (Suc n) cs [] (SkipBackward s) m = m" (*no opening [*)
by pat_completeness auto

termination bounded_machine
apply(relation "measure (\<lambda>(n, cs, rs, skipper, tape, io).
      case skipper of NoSkip \<Rightarrow> n + length cs + length rs
                   |  SkipForward s \<Rightarrow> (length cs) + n + (if s = 0 then length rs else xs)
                   |  SkipBackward s \<Rightarrow> length rs + g n)")
apply(simp)
apply(simp_all)
apply(simp_all add: min_def max_def split: nat.split)
oops
*)

lemma eval_bf_tape_shift_right: "eval_bf [instr.Right] (Normal tpe inp outp) (Normal (tape_shift_right tpe) inp outp)"
  apply(cases tpe, rename_tac l c r)
  apply(case_tac r)
  apply(auto intro: eval_bf.intros)
  done

lemma eval_bf_tape_shift_left': 
      "tape_shift_left' tpe = Result shifted_tape \<Longrightarrow>
        eval_bf [instr.Left] (Normal tpe inp outp) (Normal shifted_tape inp outp)"
  apply(cases tpe, rename_tac l c r)
  apply(case_tac l)
  apply(auto intro: eval_bf.intros)
  done

lemma eval_bf_intro_In_EOF:
  "eval_bf [In] (Normal (Tape lt c rt) (Input []) outp) (Normal (Tape lt EOF rt) (Input []) outp)"
  apply(subgoal_tac "EOF = -1")
   using eval_bf.intros(9) apply (metis diff_0)
  apply(simp add: EOF_def)
  done

lemma "(\<And>cs' rs' lt' c' rt' inp' outp'.
           skip_loop_forward cs (Loop # rs) 0 = Result (cs', rs') \<Longrightarrow>
           bounded_machine n cs' rs' (tpe, Buffer inp read_byte outp) = Result (Tape lt' c' rt', Buffer inp' read_byte outp') \<Longrightarrow>
           eval_bf cs' (Normal tpe (Input inp) (Output outp)) (Normal (Tape lt' c' rt') (Input inp') (Output outp'))) \<Longrightarrow>
       (case skip_loop_forward cs (Loop # rs) 0 of either.Error err \<Rightarrow> either.Error (err, rev rs, cs, tpe, Buffer inp read_byte outp)
        | Result (cs', rs') \<Rightarrow> bounded_machine n cs' rs' (tpe, Buffer inp read_byte outp)) =
       Result (Tape lt' c' rt', Buffer inp' read_byte outp') \<Longrightarrow>
       cur tpe = 0 \<Longrightarrow> eval_bf (Loop # cs) (Normal tpe (Input inp) (Output outp)) (Normal (Tape lt' c' rt') (Input inp') (Output outp'))"
apply(case_tac "skip_loop_forward cs (Loop # rs) 0")
apply(simp;fail)
apply(simp)
apply(rename_tac x2, case_tac x2)
apply(simp)
apply(frule skip_loop_forward_Result_Pool)
apply(induction cs)
apply(simp; fail)
apply(simp)
oops

lemma "bounded_machine limit prog rs (tpe, Buffer inp read_byte outp) = Result (Tape lt' c' rt', Buffer inp' read_byte outp')
       (*buf = Buffer inp read_byte outp *)(*\<Longrightarrow> rs = []*)
        \<Longrightarrow> 
        eval_bf prog (Normal tpe (Input inp) (Output outp))  (Normal (Tape lt' c' rt') (Input inp') (Output outp'))"
  thm bounded_machine.induct
(*It won't work anyway because the case where prog starts with Pool is unprovable
  the lemma needs to use rs too!*)
  apply(induction limit prog rs "(tpe, Buffer inp read_byte outp)" arbitrary: tpe lt' c' rt' inp inp' outp' outp rule: bounded_machine.induct)
  apply(simp_all)
  apply(auto intro: eval_bf.intros)[1]
  apply(rule_tac s'="Normal (Tape (left tape) (cur tape + 1) (right tape)) (Input inp) (Output outp)" in seq')
  apply(case_tac tape)
  apply(auto intro: eval_bf.intros)[2]
  apply(rule_tac s'="Normal (Tape (left tape) (cur tape - 1) (right tape)) (Input inp) (Output outp)" in seq')
  apply(case_tac tape)
  apply(auto intro: eval_bf.intros)[2]
  apply(case_tac "tape_shift_left' tape")
  apply(auto intro: eval_bf.intros)[1]
  apply(simp)
  apply(rename_tac "shifted_tape")
  apply(rule_tac s'="Normal shifted_tape (Input inp) (Output outp)" in seq')
  apply(auto intro: eval_bf.intros eval_bf_tape_shift_left')[2]
  apply(rule_tac s'="Normal (tape_shift_right tape) (Input inp) (Output outp)" in seq')
  apply(auto simp add: eval_bf_tape_shift_right intro: eval_bf.intros)[2]
  
  apply(case_tac inp)
  apply(rule_tac s'="Normal (Tape (left tape) EOF (right tape)) (Input inp) (Output outp)" in seq')
  apply(case_tac tape)
  apply(auto intro: eval_bf_intro_In_EOF)[2]
  apply(rename_tac i inplist)
  apply(rule_tac s'="Normal (Tape (left tape) i (right tape)) (Input inplist) (Output outp)" in seq')
  apply(case_tac tape)
  apply(auto intro: eval_bf.intros)[2]

  apply(rule_tac s'="Normal tape (Input inp) (Output (cur tape # outp))" in seq')
  apply(case_tac tape)
  apply(auto intro: eval_bf.intros)[2]

  apply(case_tac "cur tpe = 0")
  apply(simp_all)
  apply(thin_tac "(\<And>lt' c' rt' inp' outp'.
           False \<Longrightarrow>
           _ lt' c' rt' inp' outp'\<Longrightarrow>
           _ lt' c' rt' inp' outp')")
  apply(simp split: either.split_asm)
  
  oops


lemma bounded_machine_eval_bf_empty: 
      "(\<exists>limit. bounded_machine limit [] rs (tpe, Buffer inp read_byte outp) = Result (tpe', Buffer inp' read_byte outp'))
       \<longleftrightarrow>
       eval_bf [] (Normal tpe (Input inp) (Output outp))  (Normal tpe' (Input inp') (Output outp'))"
apply(rule iffI)
 apply(elim exE, rename_tac limit)
 apply(case_tac limit)
  apply(simp; fail)
 apply(simp)
 apply(auto intro: eval_bf.intros)[1]
apply(erule b_bf_init)
apply(simp)
apply(rule_tac x=1 in exI)
apply(simp; fail)
done

definition "initstatecomply cs tpe_init tpe_init' inp_init inp_init' outp_init outp_init' \<equiv>
  (\<exists>limit. bounded_machine limit cs [] (tpe_init, Buffer inp_init read_byte outp_init) = Result (tpe_init', Buffer inp_init' read_byte outp_init'))
   \<and> (*formerly was: \<longleftrightarrow>*)
   eval_bf cs (Normal tpe_init (Input inp_init) (Output outp_init))  (Normal tpe_init' (Input inp_init') (Output outp_init'))"

(*initstatecomply can be used in the induction to generalize and strengthen the IH*)
lemma "initstatecomply [] tpe_init tpe_init inp_init inp_init outp_init outp_init"
apply(simp add: initstatecomply_def)
apply(rule conjI)
 apply(rule_tac x=1 in exI)
 apply(simp; fail)
apply(auto intro: eval_bf.intros)[1]
done

lemma "bounded_machine n cs rs (tpe_init', Buffer inp_init' read_byte outp_init') = Result (tpe', Buffer inp' read_byte outp') \<Longrightarrow>
(\<exists>limit. bounded_machine limit (rev rs) [] (tpe_init, Buffer inp_init read_byte outp_init) = 
            Result (tape, Buffer inp_init' read_byte outp_init'))"
oops


lemma bounded_machine_moreSteps: 
      "bounded_machine n cs rs m = Result m' \<Longrightarrow> 
          bounded_machine (n + n') cs rs m = Result m'"
apply(induction n cs rs m
        arbitrary: m'
        rule: bounded_machine.induct)
apply(simp_all split: either.split_asm split_if_asm)
apply auto
done

lemma bounded_machine_moreSteps_helper: 
      "bounded_machine n cs rs m = Result m' \<Longrightarrow> 
          bounded_machine (Suc (x + n)) cs rs m = Result m'"
apply(induction n cs rs m
        arbitrary: m'
        rule: bounded_machine.induct)
apply(simp_all split: either.split_asm split_if_asm)
apply auto
done

lemma bounded_machine_SucD: 
      "bounded_machine n cs rs m = Result m' \<Longrightarrow> 
          bounded_machine (Suc n) cs rs m = Result m'"
apply(induction n cs rs m
        arbitrary: m'
        rule: bounded_machine.induct)
apply(simp_all split: either.split_asm split_if_asm)
apply auto
done

lemma "bounded_machine n1 cs rs (tpe, Buffer inp read_byte outp) = Result (tpe', Buffer inp' read_byte outp') \<Longrightarrow>
   bounded_machine n2 (rev rs) [] (tpe_init, Buffer inp_init read_byte outp_init) = Result (tpe, Buffer inp read_byte outp) \<Longrightarrow>
  bounded_machine (n1+n2) (rev rs @ cs) [] (tpe_init, Buffer inp_init read_byte outp_init) = Result (tpe', Buffer inp' read_byte outp')"
apply(induction n1 cs rs "(tpe, Buffer inp read_byte outp)"
        arbitrary: tpe tpe' inp inp' outp outp' tpe_init inp_init outp_init n2 
        rule: bounded_machine.induct)
apply(simp_all)
apply(rule bounded_machine_moreSteps_helper)
apply(simp; fail)
oops

lemma initstatecomply_revrsE: "initstatecomply (rev rs) tpe_init tpe_init' inp_init inp_init' outp_init outp_init'
   \<Longrightarrow>
   bounded_machine n cs rs (tpe_init', Buffer inp_init' read_byte outp_init') = Result (tpe', Buffer inp' read_byte outp') \<Longrightarrow>
   eval_bf cs (Normal tpe_init' (Input inp_init') (Output outp_init')) (Normal tpe' (Input inp') (Output outp'))
   \<Longrightarrow>
   eval_bf (rev rs @ cs) (Normal tpe_init (Input inp_init) (Output outp_init)) (Normal tpe' (Input inp') (Output outp'))"
apply(rule_tac s'="Normal tpe_init' (Input inp_init') (Output outp_init')" in seq)
 apply(simp_all)
apply(simp add: initstatecomply_def)
(*
apply(subgoal_tac "\<exists>limit. bounded_machine limit (rev rs) [] (tpe_init, Buffer inp_init read_byte outp_init) =
             Result (tpe_init', Buffer inp_init' read_byte outp_init')")
 apply blast
apply(simp add: initstatecomply_def[symmetric])
(*good until here*)
apply(thin_tac "initstatecomply _ _ _ _ _ _ _ ")
apply(induction n cs rs "(tpe_init', Buffer inp_init' read_byte outp_init')" rule: bounded_machine.induct)
apply(simp_all)
apply(auto dest: eval_bf_emptyD)[1]
apply(rule_tac x=1 in exI)
apply(simp)
oops*)
done

lemma "initstatecomply (rev rs) tpe_init tpe_init' inp_init inp_init' outp_init outp_init'
  \<Longrightarrow>
  bounded_machine limit prog rs (tpe_init', Buffer inp_init' read_byte outp_init') = Result (tpe', Buffer inp' read_byte outp')
    \<Longrightarrow> 
    eval_bf (rev rs @ prog) (Normal tpe_init (Input inp_init) (Output outp_init))  (Normal tpe' (Input inp') (Output outp'))"
  apply(induction limit prog rs "(tpe_init', Buffer inp_init' read_byte outp_init')"
          arbitrary: tpe_init tpe_init' tpe' inp_init' inp' outp' outp_init'
          rule: bounded_machine.induct)
  apply(simp; fail)
  apply(simp)
  apply(erule initstatecomply_revrsE[where cs="[]" and n="1", simplified])
  apply(auto intro: eval_bf.intros)[2]

  apply(simp)

  apply(rule_tac n="(Suc n)" in initstatecomply_revrsE, simp, simp)
  apply(rule_tac s'="Normal (Tape (left tape) (cur tape + 1) (right tape)) (Input inp_init') (Output outp_init')" in seq')
  apply(case_tac tape)
  apply(auto intro: eval_bf.intros)[2]
  oops



lemma "bounded_machine limit prog rs (tpe, buf) = Result result
        \<Longrightarrow> 
        interp_bf (prog, []) (tpe, buf) = result"
  apply(induction limit prog rs "(tpe, buf)" arbitrary:result tpe buf rule: bounded_machine.induct)
  apply(simp_all)
  apply(simp_all add: interp_bf.simps)[5]
  apply(simp add: interp_bf.simps)
  oops


lemma interp_bf_fst_emptystack: "interp_bf (i#is, []) m =
  (case i of Loop \<Rightarrow> if cur (fst m) = 0 then interp_bf (skip_loop is 1, []) m else interp_bf (is, [Loop # is]) m |
             Pool \<Rightarrow> m |
             _ \<Rightarrow> interp_bf (is, []) (next_machine i m))"
  by(simp add: interp_bf.simps split: instr.split)

lemma "interp_bf (code @ code', []) m = interp_bf (code', []) (interp_bf (code, []) m)"
  apply(induction code arbitrary: code' m)
   apply(simp add: interp_bf.simps; fail)
  apply(simp add: interp_bf_fst_emptystack)
  apply(safe)
  apply(simp split: instr.split)
  apply(safe)
  apply (simp_all add: case_prod_beta)
  (*damn you skip_loop*)
  oops

lemma "eval_bf prog (Normal (Tape [] 0 []) (Input inp) (Output []))  (Normal (Tape lt' c' rt') (Input inp') (Output outp')) \<Longrightarrow>
         interp_bf (prog, []) (Tape [] 0 [], Buffer inp read_byte []) = (Tape lt' c' rt', Buffer inp' read_byte outp')"
  apply(induction prog "(Normal (Tape [] 0 []) (Input inp) (Output []))"  "(Normal (Tape lt' c' rt') (Input inp') (Output outp'))" rule: eval_bf.induct)
  apply(simp_all add: interp_bf.simps del: next_machine.simps)[7]
  apply (simp_all add: case_prod_beta)[4]
  apply(simp add: EOF_def, fastforce)
  apply(case_tac "(read_byte inp)")
  apply fastforce
  prefer 2
  apply(simp add: interp_bf.simps; fail)
  oops


lemma "eval_bf prog (Normal (Tape [] 0 []) (Input inp) (Output outp))  (Normal (Tape lt' c' rt') (Input inp') (Output outp')) \<Longrightarrow>
          (run_bf prog inp) @ outp = outp'"
  apply(induction prog "(Normal (Tape [] 0 []) (Input inp) (Output outp))"  "(Normal (Tape lt' c' rt') (Input inp') (Output outp'))" rule: eval_bf.induct)
  apply(simp_all add: interp_bf.simps run_bf_def empty_tape_def init_table_def)
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
