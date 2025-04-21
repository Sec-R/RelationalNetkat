%{
open RN
%}

%token EOF
%token <char> SYMBOL
%token EMPTY
%token EPSILON
%token LPAR
%token RPAR
%token LBRACKET
%token RBRACKET
%token ID
%token ANY
%token COMPOSE
%token PLUS
%token TIMES
%token INTER
%token NEGATE
%token COMPLEMENT
%token STAR

%left PLUS
%left INTER
%left TIMES
%nonassoc NEGATE
%nonassoc COMPLEMENT
%nonassoc STAR

/* Types */

%type <RN.Rel.t> relation
%type <RN.Rel.t> rels
%type <RN.Rel.t> rel
%type <RN.NK.t> nk
%type <RN.pred> symbol
%type <RN.pred> or_symbols
%type <RN.NK.t> nks
%start relation

%%

relation:
  | rels EOF { RN.Rel.SeqR (RN.Rel.Nil Id,$1) }
  ;

rels:
  | rel relation { RN.Rel.SeqR ($1, $2) }
  | rel { $1 }
  ;


rel:
  | nks TIMES nks { RN.Rel.Binary ($1, $3) }
  | ID LPAR nks RPAR { RN.Rel.Id ($3) }
  | rel PLUS rel { match ($1,$3) with
                    | (RN.Rel.OrR rs1,RN.Rel.OrR rs2) -> RN.Rel.OrR (RN.SR.union rs1 rs2)
                    | (RN.Rel.OrR rs1,r) -> RN.Rel.OrR (RN.SR.add r rs1)
                    | (r,RN.Rel.OrR rs2) -> RN.Rel.OrR (RN.SR.add r rs2)
                    | (r1,r2) -> RN.Rel.OrR (RN.SR.add r1 (RN.SR.add r2 RN.SR.empty)) }
  | rel STAR { RN.Rel.StarR ($1) }
  | ID LPAR nks RPAR COMPOSE rel { RN.Rel.IdComp (Some $3, $6) }
  | EMPTY {RN.Rel.Nil (Binary (False,False))}
  | EPSILON {RN.Rel.Nil (Binary (True,True))}
  | LPAR rel RPAR { $2 }
  ;

symbol:
  | c = SYMBOL { RN.parse_char_to_pred c }
  | ANY {True}
  ;

or_symbols:
  | symbol { $1 }
  | or_symbols symbol { RN.Or ($1, $2) }
  ;

nks:
  | nks nk { RN.NK.Seq ($1, RN.NK.Seq (Dup,$2)) }
  | nk { $1 }
  ;

nk:
 | symbol {RN.NK.Pkr (Binary(True,Neg ($1)))}
 | LBRACKET NEGATE or_symbols RBRACKET { RN.NK.Pkr (Binary(True,Neg ($3))) }
 | nk PLUS nk { match ($1,$3) with
                    | (RN.NK.Union ks1,RN.NK.Union ks2) -> RN.NK.Union (RN.SNK.union ks1 ks2)
                    | (RN.NK.Union ks1,nk) -> RN.NK.Union (RN.SNK.add nk ks1)
                    | (nk,RN.NK.Union ks2) -> RN.NK.Union (RN.SNK.add nk ks2)
                    | (nk1,nk2) -> RN.NK.Union (RN.SNK.add nk1 (RN.SNK.add nk2 RN.SNK.empty)) }
  | nk STAR { RN.NK.Star ($1) }
  | nk INTER nk {RN.NK.Inter ($1,$3)}
  | COMPLEMENT nk {RN.NK.Diff (RN.NK.Seq(RN.NK.Star (RN.NK.Seq (RN.NK.Pkr (Binary (True,True)),RN.NK.Dup)),RN.NK.Pkr (Binary (True,True))),$2)}
  | EMPTY {RN.NK.Pkr (Binary (False,False))}
  | EPSILON {RN.NK.Pkr Id}
  ;   
  