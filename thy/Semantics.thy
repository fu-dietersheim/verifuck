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
       "eval_bf [In]  (Normal (Tape lt _ rt) (Input []) outp)       (Normal (Tape lt (0 - 1) rt) (Input []) outp)" | (*really?*)
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


lemma "bounded_machine limit prog rs (tpe, buf) = Result (Tape lt' c' rt', Buffer inp' read_byte outp') \<Longrightarrow>
       buf = Buffer inp read_byte outp \<Longrightarrow> rs = []
        \<Longrightarrow> 
        eval_bf prog (Normal tpe (Input inp) (Output outp))  (Normal (Tape lt' c' rt') (Input inp') (Output outp'))"
  thm bounded_machine.induct
  apply(induction limit prog rs "(tpe, buf)" rule: bounded_machine.induct)
  apply(simp_all)
  apply(auto intro: eval_bf.intros)
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
