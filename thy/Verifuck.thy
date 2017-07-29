theory Verifuck
imports
  Main
  "~~/src/HOL/Word/Word"
  "~~/src/HOL/Library/Code_Char"
  (*"~~/src/HOL/Library/Monad_Syntax"*)
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
[simp]: "tape_map_cur f tape = Tape (left tape) (f (cur tape)) (right tape)"

fun tape_shift_right :: "'a::zero tape \<Rightarrow> 'a tape" where
"tape_shift_right (Tape l c []) = Tape (c # l) 0 []" |
"tape_shift_right (Tape l c (r # rs)) = Tape (c # l) r rs"

fun tape_shift_left :: "'a::zero tape \<Rightarrow> 'a tape" where
"tape_shift_left (Tape [] c r) = Tape [] 0 (c # r)" |
"tape_shift_left (Tape (l # ls) c r) = Tape ls l (c # r)"

datatype ('a, 'b) io = Buffer (state: 'b) (read: "'b \<Rightarrow> ('a \<times> 'b)") (out_buf: "'a list")

type_synonym ('a, 'b) machine = "'a tape \<times> ('a, 'b) io"

definition read_io :: "('a, 'b) io \<Rightarrow> ('a \<times> ('a, 'b) io)" where
[simp]: "read_io io = (let (c, state') = read io (state io) in (c, Buffer state' (read io) (out_buf io)))"

definition write_io :: "'a \<Rightarrow> ('a, 'b) io \<Rightarrow> ('a, 'b) io" where
[simp]: "write_io c io = Buffer (state io) (read io) (c # out_buf io)"

type_synonym instr_table = "instr list \<times> instr list list"

definition init_table :: "instr list \<Rightarrow> instr_table" where
"init_table xs = (xs, [])"

fun next_machine :: "instr \<Rightarrow> ('a::{zero,one,minus,plus}, 'b) machine \<Rightarrow> ('a, 'b) machine" where
"next_machine Incr = apfst (tape_map_cur (\<lambda>x. x + 1))" |
"next_machine Decr = apfst (tape_map_cur (\<lambda>x. x - 1))" |
"next_machine Left = apfst tape_shift_left" |
"next_machine Right = apfst tape_shift_right" |
"next_machine In = (\<lambda>(tape, io). let (c, io') = read_io io in (tape_map_cur (\<lambda>_. c) tape, io'))" |
"next_machine Out = (\<lambda>(tape, io). (tape, write_io (cur tape) io))"

fun skip_loop :: "instr list \<Rightarrow> nat \<Rightarrow> instr list" where
"skip_loop xs 0 = xs" |
"skip_loop (Loop # xs) n = skip_loop xs (n + 1)" |
"skip_loop (Pool # xs) n = skip_loop xs (n - 1)" |
"skip_loop (x # xs) n = skip_loop xs n" |
"skip_loop [] n = []"

partial_function (tailrec) interp_bf :: "instr_table \<Rightarrow> ('a::{zero,one,minus,plus}, 'b) machine \<Rightarrow> ('a, 'b) machine" where
"interp_bf tab m =
  (case tab of ([], _) \<Rightarrow> m |
               (Loop # is, stack) \<Rightarrow> if cur (fst m) = 0 then interp_bf (skip_loop is 1, stack) m else interp_bf (is, (Loop # is) # stack) m |
               (Pool # _, is # stack) \<Rightarrow> interp_bf (is, stack) m |
               (Pool # _, []) \<Rightarrow> m |
               (i # is, stack) \<Rightarrow> interp_bf (is, stack) (next_machine i m))"

declare interp_bf.simps[code]

(*undefined behavior if reading from undefined input buffer. Pretty unusable since we cannot
  query from within our bf-code whether there is something to read available.*)
definition run_bf_generic :: "instr list \<Rightarrow> 'a::{zero,one,minus,plus} list \<Rightarrow> 'a list" where
"run_bf_generic prog input = rev (out_buf (snd (interp_bf (init_table prog)
                                  (empty_tape, (Buffer input (case_list undefined Pair) [])))))"


(*https://en.wikipedia.org/wiki/Brainfuck#End-of-file_behavior*)
definition EOF :: "8 word" where
  "EOF \<equiv> 255"
fun read_byte :: "8 word list \<Rightarrow> (8 word \<times> 8 word list)" where
  "read_byte [] = (EOF, [])" |
  "read_byte (b#bs) = (b, bs)"

definition run_bf :: "instr list \<Rightarrow> 8 word list \<Rightarrow> 8 word list" where
"run_bf prog input = rev (out_buf (snd (interp_bf (init_table prog)
                                  (empty_tape, (Buffer input read_byte [])))))"

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









datatype ('a, 'b) either = Error 'a | Result 'b


fun tape_shift_left' :: "'a tape \<Rightarrow> (string, 'a tape) either" where
"tape_shift_left' (Tape [] c r) = Error ''cannot shift tape left: end of tape''" |
"tape_shift_left' (Tape (l # ls) c r) = Result (Tape ls l (c # r))"


fun skip_loop_forward :: "instr list \<Rightarrow> instr list \<Rightarrow> nat \<Rightarrow> (string, instr list \<times> instr list) either" where
"skip_loop_forward [] rs _ = Error ''unbalanced [] expected ]''" |
"skip_loop_forward (Pool # cs) rs 0 = Result (cs, Pool#rs)" |
"skip_loop_forward (Pool # cs) rs (Suc n) = skip_loop_forward cs (Pool#rs) n" |
"skip_loop_forward (Loop # cs) rs n = skip_loop_forward cs (Loop#rs) (n + 1)"  |
"skip_loop_forward (c # cs) rs n = skip_loop_forward cs (c#rs) n"

fun skip_loop_backward :: "instr list \<Rightarrow> instr list \<Rightarrow> nat \<Rightarrow> (string, instr list \<times> instr list) either" where
"skip_loop_backward cs [] _ = Error ''unbalanced [] expected [''" |
"skip_loop_backward cs (Loop # rs) 0 = Result (Loop#cs, rs)" |
"skip_loop_backward cs (Loop # rs) (Suc n) = skip_loop_backward (Loop#cs) rs n" |
"skip_loop_backward cs (Pool # rs) n = skip_loop_backward (Pool#cs) rs (n + 1)"  |
"skip_loop_backward cs (c#rs) n = skip_loop_backward (c#cs) rs n" 

lemma skip_loop_forward_Result_Pool: "skip_loop_forward cs rs n = Result (cs', rs') \<Longrightarrow>
       hd rs' = Pool"
by(induction cs rs n arbitrary: cs' rs' rule: skip_loop_forward.induct) auto

lemma "skip_loop_backward cs rs n = Result (cs', rs') \<Longrightarrow>
       hd cs' = Loop"
by(induction cs rs n arbitrary: cs' rs' rule: skip_loop_backward.induct) auto

lemma "skip_loop_forward cs rs n = Result (cs', rs') \<Longrightarrow>
        rev rs @ cs = rev rs' @ cs'"
by(induction cs rs n arbitrary: cs' rs' rule: skip_loop_forward.induct) auto

lemma "skip_loop_backward cs rs n = Result (cs', rs') \<Longrightarrow>
        rev rs @ cs = rev rs' @ cs'"
by(induction cs rs n arbitrary: cs' rs' rule: skip_loop_backward.induct) auto

value "skip_loop_forward [Incr, Incr, Pool, Incr] [Loop, Decr] 0"
value "skip_loop_backward [Pool, Decr] [Incr, Incr, Loop, Incr] 0"


(*steps left \<Rightarrow> current program \<Rightarrow> executed instructions \<Rightarrow> skip because we are in a loop? \<Rightarrow> ...*)
fun  bounded_machine :: "nat \<Rightarrow> instr list \<Rightarrow> instr list \<Rightarrow> 
                          ('a::{zero,one,minus,plus}, 'b) machine \<Rightarrow>
                          ((string \<times> instr list \<times> instr list \<times> ('a, 'b) machine),
                           ('a, 'b) machine)
                          either" where
"bounded_machine 0 cs rs m  = Error (''Out of Instructions'', rev rs, cs, m)" | (*TODO: error out-of-instructions*)
"bounded_machine _ [] _ m  = Result m" |
"bounded_machine (Suc n) (Incr#cs) rs (tape, io) = bounded_machine n cs (Incr#rs) (tape_map_cur (\<lambda>x. x + 1) tape, io)" |
"bounded_machine (Suc n) (Decr#cs) rs (tape, io) = bounded_machine n cs (Decr#rs) (tape_map_cur (\<lambda>x. x - 1) tape, io)" |
"bounded_machine (Suc n) (Left#cs) rs (tape, io) = (case tape_shift_left' tape
                                                          of Result tape' \<Rightarrow> bounded_machine n cs (Left#rs) (tape', io)
                                                          |  Error err \<Rightarrow> Error (err, rev rs, cs, (tape, io))
                                                   )" |
"bounded_machine (Suc n) (Right#cs) rs (tape, io) = bounded_machine n cs (Right#rs) (tape_shift_right tape, io)" |
"bounded_machine (Suc n) (In#cs) rs (tape, io) = bounded_machine n cs (In#rs)
                                            (let (c, io') = read_io io in (tape_map_cur (\<lambda>_. c) tape, io'))" |
"bounded_machine (Suc n) (Out#cs) rs (tape, io) = bounded_machine n cs (Out#rs) (tape, write_io (cur tape) io)" |
"bounded_machine (Suc n) (Loop#cs) rs m = (if cur (fst m) = 0 then 
                                           (case skip_loop_forward cs (Loop#rs) 0 of
                                                   Result (cs', rs') \<Rightarrow> bounded_machine n cs' rs' m
                                                 | Error err \<Rightarrow> Error (err, rev rs, cs, m))
                                          else bounded_machine n cs (Loop#rs) m)" |
"bounded_machine (Suc n) (Pool#cs) rs m = (case skip_loop_backward (Pool#cs) rs 0 of
                                                   Result (cs', rs') \<Rightarrow> bounded_machine n cs' rs' m
                                                 | Error err \<Rightarrow> Error (err, rev rs, cs, m))"

value "bounded_machine 10 [Incr, Loop, Incr, Pool] [] (empty_tape, Buffer [] read_byte [])"

value "bounded_machine 40 [Incr, Loop, Incr, Out, Pool] [] (empty_tape, Buffer [] read_byte [])"

value "bounded_machine 40000 [Decr, Loop, Loop, Decr, Right, Incr, Left, Pool, Out, Decr, Pool] [] (empty_tape, Buffer [] read_byte [])"

value "bounded_machine limit prog [] (empty_tape, Buffer input read_byte [])"

definition run_bf_bounded :: "nat \<Rightarrow> instr list \<Rightarrow> 8 word list \<Rightarrow>
    (string \<times> instr list \<times> instr list \<times> (8 word, 8 word list) machine, 8 word list) either" where
"run_bf_bounded limit prog input \<equiv> case bounded_machine limit prog [] (empty_tape, Buffer input read_byte [])
    of Result (tape, buf) \<Rightarrow> Result (rev (out_buf buf))
    |  Error err \<Rightarrow> Error err"


lemma "case run_bf_bounded 1024 (parse_instrs hello_world) [] of Result result \<Rightarrow>
         map byte_to_char result = ''Hello World!'' @ [CHR ''\<newline>'', CHR 0x0D]" by eval

end
