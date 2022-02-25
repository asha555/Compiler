(**************************************************************************)
(* AU compilation.                                                        *)
(* Skeleton file -- expected to be modified as part of the assignment     *)
(* Do not distribute                                                      *)
(**************************************************************************)

(*I'm NOT saying that I'm the coolest girl in the world, but...!!!!!!!!!!!!!!*)
(* Jeg snaker Dansker*)
(*Di pizza ær fardig i di minutå*)
(*Don't fear! Asha is here!*)
(*Yo, bo, ho*)

{
  open Tigerparser.Parser  
  exception Error of string
  let error lexbuf msg =
    let position = Lexing.lexeme_start_p lexbuf in
    let err_str = Printf.sprintf "Lexing error in file %s at position %d:%d\n"
                  position.pos_fname position.pos_lnum (position.pos_cnum - position.pos_bol + 1)
                  ^ msg ^ "\n" in
    raise (Error err_str)
} 

let digits=['0'-'9']+
let digits_3=['0'-'9']['0'-'9']['0'-'9']
let invalid_ident=['0'-'9']+['_''a'-'z''A'-'Z']+['_''0'-'9''a'-'z''A'-'Z']*
let ident=['a'-'z''A'-'Z']['_''0'-'9''a'-'z''A'-'Z']* 
let str_char=[' '-'['] | [']'-'~']
 (*Should whitespaces include form feed? '\x0C'*)
let set_one=['@'-'_']
let set_two=['a'-'z']
(*\^? -> \127*)


(* add more named regexps here *)

rule token = parse
    [' ' '\t' ]         { token lexbuf }     (* skip blanks *)
  | eof                 { EOF }
  | '^'                 { CARET }
  | ','                 { COMMA }
  | ';'                 { SEMICOLON }
  | ":="                { ASSIGN }
  | ":"                 { COLON }
  | "."                 { DOT }
  | "("                 { LPAREN }
  | ")"                 { RPAREN }
  | "["                 { LBRACK }   
  | "]"                 { RBRACK }
  | "{"                 { LBRACE }
  | "}"                 { RBRACE }
  | "+"                 { PLUS }
  | "-"                 { MINUS } (* What about NEG? *)
  | "*"                 { TIMES }
  | "="                 { EQ }
  | "<>"                { NEQ }
  | "<"                 { LT }  
  | "<="                { LE }  
  | ">"                 { GT }
  | ">="                { GE }
  | "&"                 { AND }
  | "|"                 { OR }
  | "while"             { WHILE }
  | "for"               { FOR }
  | "to"                { TO }
  | "break"             { BREAK }
  | "let"               { LET }
  | "end"               { END }
  | "function"          { FUNCTION }
  | "var"               { VAR }
  | "type"              { TYPE }
  | "array"             { ARRAY }
  | "if"                { IF }
  | "then"              { THEN }
  | "else"              { ELSE }
  | "do"                { DO }
  | "of"                { OF }
  | "nil"               { NIL }
  | "in"                { IN }
  | '"'                 { stringHandler lexbuf.lex_start_p (Buffer.create 32) lexbuf}
  | '\n'                { Lexing.new_line lexbuf; token lexbuf }  
  | "//"                { single_line_comment lexbuf }
  | "/*"                { multi_line_comment 0 lexbuf }
  | '/'                 { DIVIDE }
  | invalid_ident as i  { error lexbuf ("Invalid identifier: Identifiers should begin with a letter, not a number. "^i) }
  | ident as i          { ID i }
  | digits as i         { INT (match int_of_string_opt i with
                          | None   -> error lexbuf "Invalid integer value."
                          | Some i -> i) }
  | _ as t              { error lexbuf ("Invalid character '" ^ (String.make 1 t) ^ "'") }

and single_line_comment = parse
  eof       { EOF }
| '\n'      { token lexbuf }
| _		      { single_line_comment lexbuf }

and multi_line_comment level = parse
  eof     { error lexbuf "Missing close of multi-line-comment" }
| "*/"		{ if level = 0 then token lexbuf else multi_line_comment (level - 1) lexbuf }
| "/*"		{ multi_line_comment (level + 1) lexbuf }
| '\n'    { Lexing.new_line lexbuf; multi_line_comment level lexbuf }
| _		    { multi_line_comment level lexbuf }

and stringHandler start_pos buf = parse
  eof                           { error lexbuf "Premature occurence of EOF. Missing close of string" }
| '"'                           { lexbuf.lex_start_p <- start_pos; STRING (Buffer.contents buf) }
| '\\''r''\\''n'                { Buffer.add_string buf "\r\n"; stringHandler start_pos buf lexbuf }
| '\\''r'                       { Buffer.add_char buf '\r'; stringHandler start_pos buf lexbuf }
| '\\''n'                       { Buffer.add_char buf '\n'; stringHandler start_pos buf lexbuf }
| '\\''t'                       { Buffer.add_char buf '\t'; stringHandler start_pos buf lexbuf }
| '\\''"'                       { Buffer.add_char buf '\"'; stringHandler start_pos buf lexbuf }
| '\\''^'(set_one as c)         { Buffer.add_char buf (Char.chr(Char.code(c)-64)); stringHandler start_pos buf lexbuf }
| '\\''^'(set_two as c)         { Buffer.add_char buf (Char.chr(Char.code(c)-96)); stringHandler start_pos buf lexbuf }
| '\\''^''?'                    { Buffer.add_char buf (Char.chr(127)); stringHandler start_pos buf lexbuf }
| '\\'(digits_3 as ddd)         { Buffer.add_char buf (let value = int_of_string ddd in if value >= 0 && value < 256 then Char.chr(value) else error lexbuf (Printf.sprintf "ASCII octal code out of range: was '" ^ ddd ^ "' but should be [0:255]")); stringHandler start_pos buf lexbuf }
| '\\''\\'                      { Buffer.add_char buf '\\'; stringHandler start_pos buf lexbuf }
| '\\'                          { empty_space start_pos buf lexbuf }
| str_char as c                 { Buffer.add_char buf c; stringHandler start_pos buf lexbuf }
| _ as t                        { error lexbuf ("Invalid character '" ^ (String.make 1 t) ^ "'") } 

and empty_space start_pos buf = parse
  '\\'                  { stringHandler start_pos buf lexbuf }
| eof                   { error lexbuf "Missing close of \\ ... \\, where '...' abbreviates whitespace characters" }
| '\t' | ' ' | '\b'     { empty_space start_pos buf lexbuf }
| '\n' | "\r\n" | '\r'  { Lexing.new_line lexbuf; empty_space start_pos buf lexbuf }
| _ as t                { error lexbuf ("Invalid character '" ^ (String.make 1 t) ^ "'") } 

(*
| '\\'(whitespaces as w)'\\'    { String.iter (fun c -> if c = '\n' then Lexing.new_line lexbuf) w; stringHandler start_pos buf lexbuf }


iter (c -> if c = '\n' then Lexing.new_line lexbuf) w;
(*if c = '\n' then Lexing.new_line lexbuf*)
*)