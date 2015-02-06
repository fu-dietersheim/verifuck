theory Verifuck
imports
  Main
  "~~/src/HOL/Library/Code_Char"
begin

instantiation char :: zero begin
  definition "zero_char = char_of_nat 0"
  instance ..
end

instantiation char :: one begin
  definition "one_char = char_of_nat 1"
  instance ..
end

instantiation char :: plus begin
  definition "plus_char c d = char_of_nat (nat_of_char c + nat_of_char d)"
  instance ..
end

instantiation char :: minus begin
  definition "minus_char c d = char_of_integer (integer_of_char c - integer_of_char d)"
  instance ..
end

datatype_new instr = Incr | Decr | Right | Left | Out | In | Loop | Pool

datatype_new 'a tape = Tape (left: "'a list") (cur: 'a) (right: "'a list")

definition empty_tape :: "'a::zero tape" where
"empty_tape = Tape [] 0 []"

definition tape_map_cur :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a tape \<Rightarrow> 'a tape" where
"tape_map_cur f tape = Tape (left tape) (f (cur tape)) (right tape)"

fun tape_shift_right :: "'a::zero tape \<Rightarrow> 'a tape" where
"tape_shift_right (Tape l c []) = Tape (c # l) 0 []" |
"tape_shift_right (Tape l c (r # rs)) = Tape (c # l) r rs"

fun tape_shift_left :: "'a::zero tape \<Rightarrow> 'a tape" where
"tape_shift_left (Tape [] c r) = Tape [] 0 (c # r)" |
"tape_shift_left (Tape (l # ls) c r) = Tape ls l (c # r)"

datatype_new ('a, 'b) io = Buffer (state: 'b) (read: "'b \<Rightarrow> ('a \<times> 'b)") (out_buf: "'a list")

definition init_io :: "'a list \<Rightarrow> ('a, 'a list) io" where
"init_io xs = Buffer xs (case_list undefined Pair) []"

type_synonym ('a, 'b) machine = "'a tape \<times> ('a, 'b) io"

definition read_io :: "('a, 'b) io \<Rightarrow> ('a \<times> ('a, 'b) io)" where
"read_io io = (let (c, state') = read io (state io) in (c, Buffer state' (read io) (out_buf io)))"

definition write_io :: "'a \<Rightarrow> ('a, 'b) io \<Rightarrow> ('a, 'b) io" where
"write_io c io = Buffer (state io) (read io) (c # out_buf io)"

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
               (Loop # is, stack) \<Rightarrow> if cur (fst m) = 0 then interp_bf (skip_loop is 1, stack) m else interp_bf (is, is # stack) m |
               (Pool # _, is2 # stack) \<Rightarrow> interp_bf (is2, stack) m | (* todo: codegen bug, rename is2 to is to reproduce *)
               (Pool # _, []) \<Rightarrow> m |
               (i # is, stack) \<Rightarrow> interp_bf (is, stack) (next_machine i m))"

declare interp_bf.simps[code]

export_code interp_bf in SML module_name Verifuck file "code/verifuck.ML"
(*SML_file "code/verifuck.ML"*)

value (code) "interp_bf (init_table [Incr, Left, Incr, Left, In, Out]) (empty_tape :: int tape, init_io [2])"

end
