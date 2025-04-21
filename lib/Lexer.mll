{
  open Parser
  exception Error of string
}



let epsilon = ['1']
let empty = ['0']
let symbol = ['a'-'z' 'A'-'Z']
let Id = ['I']
let star = ['*']
let plus = ['+']
let negate = ['^']
let complement = ['~']
let lpar = ['(']
let rpar = [')']
let lbracket = ['[']
let rbracket = [']']
let any = ['.']
let compose = ['o']
let whitespace = [' ' '\t']+

(* Rules *)

rule token = parse
  | " x "  { TIMES }
  | " ∩ " { INTER }
  | empty { EMPTY }
  | epsilon { EPSILON }
  | star { STAR }
  | plus { PLUS }
  | negate { NEGATE }
  | complement { COMPLEMENT }
  | lpar { LPAR }
  | rpar { RPAR }
  | lbracket { LBRACKET }
  | rbracket { RBRACKET }
  | any { ANY }
  | compose { COMPOSE }
  | Id { ID }
  | symbol as s {SYMBOL (s)}
  | whitespace { token lexbuf } 
  | eof { EOF }
  | _ { raise (Failure ("Character not allowed in source text: '" ^ Lexing.lexeme lexbuf ^ "'")) }
