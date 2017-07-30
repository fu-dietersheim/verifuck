theory Verifuck
imports
  Main
  "~~/src/HOL/Word/Word"
  "~~/src/HOL/Library/Code_Char"
begin

datatype instr = Incr | Decr | Right | Left | Out | In | Loop | Pool

fun parse_instrs :: "string \<Rightarrow> instr list" where
"parse_instrs [] = []" |
"parse_instrs (x # xs) = (
  if x = CHR ''.'' then Out # parse_instrs xs else
  if x = CHR '','' then In # parse_instrs xs else
  if x = CHR ''+'' then Incr # parse_instrs xs else
  if x = CHR ''-'' then Decr # parse_instrs xs else
  if x = CHR ''<'' then Left # parse_instrs xs else
  if x = CHR ''>'' then Right # parse_instrs xs else
  if x = CHR ''['' then Loop # parse_instrs xs else
  if x = CHR '']'' then Pool # parse_instrs xs else
  parse_instrs xs)"

datatype 'a tape = Tape (left: "'a list") (cur: 'a) (right: "'a list")

definition empty_tape :: "'a::zero tape" where
"empty_tape = Tape [] 0 []"

definition tape_map_cur :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a tape \<Rightarrow> 'a tape" where
  "tape_map_cur f tape = Tape (left tape) (f (cur tape)) (right tape)"

lemma "tape_map_cur f (Tape l c r) = Tape l (f c) r" by(simp add: tape_map_cur_def)

fun tape_shift_right :: "'a::zero tape \<Rightarrow> 'a tape" where
"tape_shift_right (Tape l c []) = Tape (c # l) 0 []" |
"tape_shift_right (Tape l c (r # rs)) = Tape (c # l) r rs"

fun tape_shift_left :: "'a::zero tape \<Rightarrow> 'a tape" where
"tape_shift_left (Tape [] c r) = Tape [] 0 (c # r)" |
"tape_shift_left (Tape (l # ls) c r) = Tape ls l (c # r)"

(*state: input buffer
  read: read from state, produce new state
  out_buf: output buffer*)
datatype ('a, 'b) io = Buffer (state: 'b) (read: "'b \<Rightarrow> ('a \<times> 'b)") ("write": "'a \<Rightarrow> 'b \<Rightarrow> 'b")

datatype ('a, 'b) machine = Machine (tape: "'a tape") (io_state: "('a, 'b) io")

definition map_tape :: "('a tape \<Rightarrow> 'a tape) \<Rightarrow> ('a, 'b) machine  \<Rightarrow> ('a, 'b) machine" where
  "map_tape f m \<equiv> Machine (f (tape m)) (io_state m)"

definition read_io :: "('a, 'b) io \<Rightarrow> ('a \<times> ('a, 'b) io)" where
  "read_io io = (let (c, state') = read io (state io) in (c, Buffer state' (read io) (write io)))"

lemma "read_io (Buffer s r out) = (fst (r s), Buffer (snd (r s)) r out)"
  by(simp add: read_io_def split: prod.splits)

definition write_io :: "'a \<Rightarrow> ('a, 'b) io \<Rightarrow> ('a, 'b) io" where
  "write_io c io = Buffer (write io c (state io)) (read io) (write io)"

(*current program \<times> stack for loop*)
type_synonym stacked_instr_list_state = "instr list \<times> instr list list"

definition init_stacked_instr_list_state :: "instr list \<Rightarrow> stacked_instr_list_state" where
  "init_stacked_instr_list_state xs = (xs, [])"

fun next_machine :: "instr \<Rightarrow> ('a::{zero,one,minus,plus}, 'b) machine \<Rightarrow> ('a, 'b) machine" where
"next_machine Incr = map_tape (tape_map_cur (\<lambda>x. x + 1))" |
"next_machine Decr = map_tape (tape_map_cur (\<lambda>x. x - 1))" |
"next_machine Left = map_tape tape_shift_left" |
"next_machine Right = map_tape tape_shift_right" |
"next_machine In = (\<lambda>m. let (c, io') = read_io (io_state m) in Machine (tape_map_cur (\<lambda>_. c) (tape m)) io')" |
"next_machine Out = (\<lambda>m. Machine (tape m) (write_io (cur (tape m)) (io_state m)))"

fun skip_loop :: "instr list \<Rightarrow> nat \<Rightarrow> (instr list) option" where
"skip_loop xs 0 = Some xs" |
"skip_loop (Loop # xs) n = skip_loop xs (n + 1)" |
"skip_loop (Pool # xs) n = skip_loop xs (n - 1)" |
"skip_loop (x # xs) n = skip_loop xs n" |
"skip_loop _ _ = None"

partial_function (tailrec) interp_bf :: "stacked_instr_list_state \<Rightarrow> ('a::{zero,one,minus,plus}, 'b) machine \<Rightarrow> (instr list list \<times> ('a, 'b) machine) option" where
"interp_bf tab m =
  (case tab of ([], stack) \<Rightarrow> Some (stack, m) |
               (Loop # is, stack) \<Rightarrow> if cur (tape m) = 0
                                     then (case skip_loop is 1 of
                                                None \<Rightarrow> None |
                                                Some is' \<Rightarrow> interp_bf (is', stack) m)
                                     else interp_bf (is, (Loop # is) # stack) m |
               (Pool # _, is # stack) \<Rightarrow> interp_bf (is, stack) m |
               (Pool # _, []) \<Rightarrow> None |
               (i # is, stack) \<Rightarrow> interp_bf (is, stack) (next_machine i m))"

declare interp_bf.simps[code]

fun loop_level :: "instr list \<Rightarrow> nat option" where
"loop_level [] = Some 0" |
"loop_level (Loop # xs) = map_option Suc (loop_level xs)" |
"loop_level (Pool # xs) = Option.bind (loop_level xs) (\<lambda>n. case n of 0 \<Rightarrow> None | Suc n \<Rightarrow> Some n)" |
"loop_level (_ # xs) = loop_level xs"

lemma loop_free_is_fold:
  "(\<forall>x \<in> set xs. x \<noteq> Pool \<and> x \<noteq> Loop) \<Longrightarrow> interp_bf (xs, stack) m = Some ((stack, fold next_machine xs m))"
by (induction xs arbitrary: m stack) (simp add: interp_bf.simps split: instr.splits)+

lemma skip_loop_loop_free: "(\<forall>x \<in> set xs. x \<noteq> Pool \<and> x \<noteq> Loop) \<Longrightarrow> skip_loop (xs @ [Pool]) 1 = Some []"
  apply (induction xs)
   apply simp
  apply simp
  apply (case_tac a)
         apply auto
  done

lemma loop_unroll:
  "(\<forall>x \<in> set xs. x \<noteq> Pool \<and> x \<noteq> Loop) \<Longrightarrow> interp_bf (Loop # xs, stack) m = Some ((stack, fold next_machine xs m))"
apply (induction xs arbitrary: m stack)
apply (subst interp_bf.simps)
apply simp
apply safe
sorry

axiomatization where falseI: "False"


(*undefined behavior if reading from undefined input buffer. Pretty unusable since we cannot
  query from within our bf-code whether there is something to read available.*)
  (*factory*)
definition run_bf_generic :: "instr list \<Rightarrow> 'a::{zero,one,minus,plus} list \<Rightarrow> 'a list" where
"run_bf_generic prog input = rev (out_buf (io_state (the (interp_bf (init_stacked_instr_list_state prog)
                                  (Machine empty_tape (Buffer input (\<lambda>inp. (hd inp, tl inp)) []))))))"


(*https://en.wikipedia.org/wiki/Brainfuck#End-of-file_behavior*)
definition EOF :: "8 word" where
  "EOF \<equiv> 255"
fun read_byte :: "8 word list \<Rightarrow> (8 word \<times> 8 word list)" where
  "read_byte [] = (EOF, [])" |
  "read_byte (b#bs) = (b, bs)"

  (*brainfuck byte factory*)
definition run_bf :: "instr list \<Rightarrow> 8 word list \<Rightarrow> 8 word list" where
"run_bf prog input = rev (out_buf (io_state (the (interp_bf (init_stacked_instr_list_state prog)
                                  (Machine empty_tape (Buffer input read_byte []))))))"

export_code run_bf in SML module_name Verifuck file "code/verifuck.ML"
(*SML_file "code/verifuck.ML"*)

(*source: http://de.wikipedia.org/wiki/Brainfuck#Hello_World.21 retrieved Feb 7 2015*)
definition "hello_world = ''++++++++++
 [
  >+++++++>++++++++++>+++>+<<<<-
 ]                       Schleife zur Vorbereitung der Textausgabe
 >++.                    Ausgabe von 'H'
 >+.                     Ausgabe von 'e'
 +++++++.                'l'
 .                       'l'
 +++.                    'o'
 >++.                    Leerzeichen
 <<+++++++++++++++.      'W'
 >.                      'o'
 +++.                    'r'
 ------.                 'l'
 --------.               'd'
 >+.                     '!'
 >.                      Zeilenvorschub
 +++.                    Wagenruecklauf''"

definition byte_to_char :: "8 word \<Rightarrow> char" where
  "byte_to_char b \<equiv> char_of_nat (unat b)"
definition char_to_byte :: "char \<Rightarrow> 8 word" where
  "char_to_byte c \<equiv> of_nat (nat_of_char c)"

lemma "let result = run_bf (parse_instrs hello_world) ([]::8 word list) in
         map byte_to_char result = ''Hello World!'' @ [CHR ''\<newline>'', CHR 0x0D]" by eval

export_code run_bf in Haskell









fun tape_shift_left' :: "'a tape \<Rightarrow> (string + 'a tape)" where
"tape_shift_left' (Tape [] c r) = Inl ''cannot shift tape left: end of tape''" |
"tape_shift_left' (Tape (l # ls) c r) = Inr (Tape ls l (c # r))"


fun skip_loop_forward :: "instr list \<Rightarrow> instr list \<Rightarrow> nat \<Rightarrow> string + (instr list \<times> instr list)" where
"skip_loop_forward [] rs _ = Inl ''unbalanced [] expected ]''" |
"skip_loop_forward (Pool # cs) rs 0 = Inr (cs, Pool#rs)" |
"skip_loop_forward (Pool # cs) rs (Suc n) = skip_loop_forward cs (Pool#rs) n" |
"skip_loop_forward (Loop # cs) rs n = skip_loop_forward cs (Loop#rs) (n + 1)"  |
"skip_loop_forward (c # cs) rs n = skip_loop_forward cs (c#rs) n"

fun skip_loop_backward :: "instr list \<Rightarrow> instr list \<Rightarrow> nat \<Rightarrow> string + (instr list \<times> instr list)" where
"skip_loop_backward cs [] _ = Inl ''unbalanced [] expected [''" |
"skip_loop_backward cs (Loop # rs) 0 = Inr (Loop#cs, rs)" |
"skip_loop_backward cs (Loop # rs) (Suc n) = skip_loop_backward (Loop#cs) rs n" |
"skip_loop_backward cs (Pool # rs) n = skip_loop_backward (Pool#cs) rs (n + 1)"  |
"skip_loop_backward cs (c#rs) n = skip_loop_backward (c#cs) rs n"

lemma skip_loop_forward_Result_Pool: "skip_loop_forward cs rs n = Inr (cs', rs') \<Longrightarrow>
       hd rs' = Pool"
by(induction cs rs n arbitrary: cs' rs' rule: skip_loop_forward.induct) auto

lemma "skip_loop_backward cs rs n = Inr (cs', rs') \<Longrightarrow>
       hd cs' = Loop"
by(induction cs rs n arbitrary: cs' rs' rule: skip_loop_backward.induct) auto

lemma skip_loop_forward_Result: "skip_loop_forward cs rs n = Inr (cs', rs') \<Longrightarrow>
        rev rs @ cs = rev rs' @ cs'"
by(induction cs rs n arbitrary: cs' rs' rule: skip_loop_forward.induct) auto
<<<<<<< Updated upstream
  
lemma skip_loop_forward_Result_cs: "skip_loop_forward cs rs n = Inr (cs', rs') \<Longrightarrow>
=======

lemma skip_loop_forward_Reuslt_cs: "skip_loop_forward cs rs n = Result (cs', rs') \<Longrightarrow>
>>>>>>> Stashed changes
       cs = (drop (length rs) (rev rs')) @ cs'"
(*  apply(induction cs rs n arbitrary: cs' rs' rule: skip_loop_forward.induct)
                 apply auto (*This proof is yolo*)
               apply (smt append.assoc append_Nil append_eq_append_conv_if append_eq_conv_conj append_is_Nil_conv append_same_eq append_take_drop_id drop_all drop_append length_rev rev.simps(2) rev_append rev_rev_ident skip_loop_forward_Reuslt)
              apply (smt append.assoc append_Nil append_eq_append_conv_if append_eq_conv_conj append_is_Nil_conv append_same_eq append_take_drop_id drop_all drop_append length_rev rev.simps(2) rev_append rev_rev_ident skip_loop_forward_Reuslt)
             apply (smt append.assoc append_Nil append_eq_append_conv_if append_eq_conv_conj append_is_Nil_conv append_same_eq append_take_drop_id drop_all drop_append length_rev rev.simps(2) rev_append rev_rev_ident skip_loop_forward_Reuslt)
            apply (smt append.assoc append_Nil append_eq_append_conv_if append_eq_conv_conj append_is_Nil_conv append_same_eq append_take_drop_id drop_all drop_append length_rev rev.simps(2) rev_append rev_rev_ident skip_loop_forward_Reuslt)
           apply (smt append.assoc append_Nil append_eq_append_conv_if append_eq_conv_conj append_is_Nil_conv append_same_eq append_take_drop_id drop_all drop_append length_rev rev.simps(2) rev_append rev_rev_ident skip_loop_forward_Reuslt)
          apply (smt append.assoc append_Nil append_eq_append_conv_if append_eq_conv_conj append_is_Nil_conv append_same_eq append_take_drop_id drop_all drop_append length_rev rev.simps(2) rev_append rev_rev_ident skip_loop_forward_Reuslt)
         apply (smt append.assoc append_Nil append_eq_append_conv_if append_eq_conv_conj append_is_Nil_conv append_same_eq append_take_drop_id drop_all drop_append length_rev rev.simps(2) rev_append rev_rev_ident skip_loop_forward_Reuslt)
        apply (smt append.assoc append_Nil append_eq_append_conv_if append_eq_conv_conj append_is_Nil_conv append_same_eq append_take_drop_id drop_all drop_append length_rev rev.simps(2) rev_append rev_rev_ident skip_loop_forward_Reuslt)
       apply (smt append.assoc append_Nil append_eq_append_conv_if append_eq_conv_conj append_is_Nil_conv append_same_eq append_take_drop_id drop_all drop_append length_rev rev.simps(2) rev_append rev_rev_ident skip_loop_forward_Reuslt)
      apply (smt append.assoc append_Nil append_eq_append_conv_if append_eq_conv_conj append_is_Nil_conv append_same_eq append_take_drop_id drop_all drop_append length_rev rev.simps(2) rev_append rev_rev_ident skip_loop_forward_Reuslt)
     apply (smt append.assoc append_Nil append_eq_append_conv_if append_eq_conv_conj append_is_Nil_conv append_same_eq append_take_drop_id drop_all drop_append length_rev rev.simps(2) rev_append rev_rev_ident skip_loop_forward_Reuslt)
    apply (smt append.assoc append_Nil append_eq_append_conv_if append_eq_conv_conj append_is_Nil_conv append_same_eq append_take_drop_id drop_all drop_append length_rev rev.simps(2) rev_append rev_rev_ident skip_loop_forward_Reuslt)
   apply (smt append.assoc append_Nil append_eq_append_conv_if append_eq_conv_conj append_is_Nil_conv append_same_eq append_take_drop_id drop_all drop_append length_rev rev.simps(2) rev_append rev_rev_ident skip_loop_forward_Reuslt)
  apply (smt append.assoc append_Nil append_eq_append_conv_if append_eq_conv_conj append_is_Nil_conv append_same_eq append_take_drop_id drop_all drop_append length_rev rev.simps(2) rev_append rev_rev_ident skip_loop_forward_Reuslt)
*)
<<<<<<< Updated upstream
  oops
    
lemma "skip_loop_backward cs rs n = Inr (cs', rs') \<Longrightarrow>
=======
  done

lemma "skip_loop_backward cs rs n = Result (cs', rs') \<Longrightarrow>
>>>>>>> Stashed changes
        rev rs @ cs = rev rs' @ cs'"
by(induction cs rs n arbitrary: cs' rs' rule: skip_loop_backward.induct) auto

value "skip_loop_forward [Incr, Incr, Pool, Incr] [Loop, Decr] 0"
value "skip_loop_backward [Pool, Decr] [Incr, Incr, Loop, Incr] 0"


<<<<<<< Updated upstream
(*steps left \<Rightarrow> current program \<Rightarrow> executed instructions \<Rightarrow> machine state \<Rightarrow> result*)
fun  bounded_machine :: "nat \<Rightarrow> instr list \<Rightarrow> instr list \<Rightarrow> 
=======
(*steps left \<Rightarrow> current program \<Rightarrow> executed instructions \<Rightarrow> skip because we are in a loop? \<Rightarrow> ...*)
fun  bounded_machine :: "nat \<Rightarrow> instr list \<Rightarrow> instr list \<Rightarrow>
>>>>>>> Stashed changes
                          ('a::{zero,one,minus,plus}, 'b) machine \<Rightarrow>
                           (string \<times> instr list \<times> instr list \<times> ('a, 'b) machine) +
                           ('a, 'b) machine
                          " where
"bounded_machine 0 cs rs m  = Inl (''Out of Instructions'', rev rs, cs, m)" | (*TODO: error out-of-instructions*)
"bounded_machine _ [] _ m  = Inr m" |
"bounded_machine (Suc n) (Incr#cs) rs (Machine tpe io) = bounded_machine n cs (Incr#rs) (Machine (tape_map_cur (\<lambda>x. x + 1) tpe) io)" |
"bounded_machine (Suc n) (Decr#cs) rs (Machine tpe io) = bounded_machine n cs (Decr#rs) (Machine (tape_map_cur (\<lambda>x. x - 1) tpe) io)" |
"bounded_machine (Suc n) (Left#cs) rs (Machine tpe io) = (case tape_shift_left' tpe
                                                          of Inr tape' \<Rightarrow> bounded_machine n cs (Left#rs) (Machine tape' io)
                                                          |  Inl err \<Rightarrow> Inl (err, rev rs, cs, (Machine tpe io))
                                                   )" |
<<<<<<< Updated upstream
"bounded_machine (Suc n) (Right#cs) rs (Machine tpe io) = bounded_machine n cs (Right#rs) (Machine (tape_shift_right tpe) io)" |
"bounded_machine (Suc n) (In#cs) rs (Machine tpe io) = bounded_machine n cs (In#rs)
                                            (let (c, io') = read_io io in (Machine (tape_map_cur (\<lambda>_. c) tpe) io'))" |
"bounded_machine (Suc n) (Out#cs) rs (Machine tpe io) = bounded_machine n cs (Out#rs) (Machine tpe (write_io (cur tpe) io))" |
"bounded_machine (Suc n) (Loop#cs) rs m = (if cur (tape m) = 0 then
=======
"bounded_machine (Suc n) (Right#cs) rs (tape, io) = bounded_machine n cs (Right#rs) (tape_shift_right tape, io)" |
"bounded_machine (Suc n) (In#cs) rs (tape, io) = bounded_machine n cs (In#rs)
                                            (let (c, io') = read_io io in (tape_map_cur (\<lambda>_. c) tape, io'))" |
"bounded_machine (Suc n) (Out#cs) rs (tape, io) = bounded_machine n cs (Out#rs) (tape, write_io (cur tape) io)" |
"bounded_machine (Suc n) (Loop#cs) rs m = (if cur (fst m) = 0 then
>>>>>>> Stashed changes
                                           (case skip_loop_forward cs (Loop#rs) 0 of
                                                   Inr (cs', rs') \<Rightarrow> bounded_machine n cs' rs' m
                                                 | Inl err \<Rightarrow> Inl (err, rev rs, cs, m))
                                          else bounded_machine n cs (Loop#rs) m)" |
"bounded_machine (Suc n) (Pool#cs) rs m = (case skip_loop_backward (Pool#cs) rs 0 of
                                                   Inr (cs', rs') \<Rightarrow> bounded_machine n cs' rs' m
                                                 | Inl err \<Rightarrow> Inl (err, rev rs, cs, m))"

value "bounded_machine 10 [Incr, Loop, Incr, Pool] [] (Machine empty_tape (Buffer [] read_byte []))"

value "bounded_machine 4000 [Incr, Loop, Incr, Out, Pool] [] (Machine empty_tape (Buffer [] read_byte []))"

value "bounded_machine 400000 [Decr, Loop, Loop, Decr, Right, Incr, Left, Pool, Out, Decr, Pool] [] (Machine empty_tape (Buffer [] read_byte []))"

value "bounded_machine limit prog [] (Machine empty_tape (Buffer input read_byte []))"

definition run_bf_bounded :: "nat \<Rightarrow> instr list \<Rightarrow> 8 word list \<Rightarrow>
    (string \<times> instr list \<times> instr list \<times> (8 word, 8 word list) machine) + (8 word list)" where
"run_bf_bounded limit prog input \<equiv> case bounded_machine limit prog [] (Machine empty_tape (Buffer input read_byte []))
    of Inr (Machine tpe buf) \<Rightarrow> Inr (rev (out_buf buf))
    |  Inl err \<Rightarrow> Inl err"


lemma "case run_bf_bounded 1024 (parse_instrs hello_world) [] of Inr result \<Rightarrow>
         map byte_to_char result = ''Hello World!'' @ [CHR ''\<newline>'', CHR 0x0D]" by eval

lemma "bounded_machine n prog rs m = Inr m' \<Longrightarrow>
 interp_bf (init_stacked_instr_list_state prog) m = Some m'"
  apply(induction n prog rs m rule: bounded_machine.induct)
    apply(simp_all add: init_stacked_instr_list_state_def interp_bf.simps map_tape_def split: list.splits)
oops

theorem "bounded_machine n prog [] m = Inr m' \<Longrightarrow>
 interp_bf (init_stacked_instr_list_state prog) m = Some m'"
  oops (*todo lars*)

end
