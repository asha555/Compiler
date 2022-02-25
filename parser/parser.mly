(**************************************************************************)
(* AU compilation.                                                        *)
(* Skeleton file -- expected to be modified as part of the assignment     *)
(* Do not distribute                                                      *)
(**************************************************************************)

%{
  open Tigercommon.Symbol
  open Tigercommon.Absyn   
  open ParserAux 
%}

%token EOF
%token <string> ID
%token <int> INT 
%token <string> STRING 
%token COMMA COLON SEMICOLON 
%token LPAREN RPAREN LBRACK RBRACK LBRACE RBRACE 
%token DOT PLUS MINUS TIMES DIVIDE EQ NEQ LT LE GT GE 
%token AND OR ASSIGN ARRAY IF THEN ELSE WHILE FOR TO DO
%token LET IN END OF BREAK NIL FUNCTION VAR TYPE CARET 
%token UNARYMINUS

%right DO OF ASSIGN ELSE THEN 
%left OR
%left AND
%nonassoc GT GE  LE LT EQ NEQ
%left PLUS MINUS 
%left TIMES DIVIDE
%left UNARYMINUS
%right CARET
(*%right CONCAT*)

%start <Tigercommon.Absyn.exp> program  
(* Observe that we need to use fully qualified types for the start symbol *)

%%
(* Expressions *)
exp_base:
| NIL                                         { NilExp }
| i=INT                                       { IntExp i }
| s=STRING                                    { StringExp s }
| BREAK                                       { BreakExp } 
| v=var                                       { VarExp v }  
| v=var ASSIGN e=exp                          { AssignExp {var=v; exp=e }}              
| WHILE t=exp DO b=exp                        { WhileExp {test=t; body=b }}
| LPAREN s=explist RPAREN                     { SeqExp s }
| id=ID LPAREN s=arglist RPAREN               { CallExp {func=symbol(id); args=s }}
| IF t1=exp THEN e1=exp ELSE e2 = exp         { IfExp {test=t1; thn=e1; els=Some e2 }}
| IF t1=exp THEN e1=exp                       { IfExp {test=t1; thn=e1; els=None }}
| LET s=list(decl) IN e = explist END         { LetExp {decls=s; body= SeqExp(e) ^! $startpos }}
| FOR i=ID ASSIGN e1=exp TO e2=exp DO e3=exp  { ForExp {var = symbol i; escape = ref true; lo=e1; hi= e2; body= e3 }}
| e1=exp PLUS     e2=exp                      { OpExp {left=e1; oper=PlusOp; right=e2 }}
| e1=exp MINUS    e2=exp                      { OpExp {left=e1; oper=MinusOp; right=e2 }}
| e1=exp TIMES    e2=exp                      { OpExp {left=e1; oper=TimesOp; right=e2 }}
| e1=exp DIVIDE   e2=exp                      { OpExp {left=e1; oper=DivideOp; right=e2 }}
| e1=exp NEQ      e2=exp                      { OpExp {left=e1; oper=NeqOp; right=e2 }}
| e1=exp EQ       e2=exp                      { OpExp {left=e1; oper=EqOp; right=e2 }}
| e1=exp CARET    e2=exp                      { OpExp {left=e1; oper=ExponentOp; right=e2 }}
| e1=exp GT       e2=exp                      { OpExp {left=e1; oper=GtOp; right=e2 }}
| e1=exp GE       e2=exp                      { OpExp {left=e1; oper=GeOp; right=e2 }}
| e1=exp LE       e2=exp                      { OpExp {left=e1; oper=LeOp; right=e2 }}
| e1=exp LT       e2=exp                      { OpExp {left=e1; oper=LtOp; right=e2 }}
| e1=exp AND      e2=exp                      { IfExp {test=e1; thn=e2; els=Some(IntExp 0 ^! $startpos) }}
| e1=exp OR       e2=exp                      { IfExp {test=e1; thn=(IntExp 1 ^! $startpos); els=Some e2 }}
| ty=ID LBRACE f=record_fields RBRACE         { RecordExp {fields=f; typ=symbol(ty) }}
| ty=ID LBRACK e1=exp RBRACK OF e2=exp        { ArrayExp {typ=symbol(ty); size=e1; init=e2 }}
| MINUS e=exp                                 { OpExp {left=IntExp 0 ^! $startpos; oper=MinusOp; right=e }} %prec UNARYMINUS

record_fields:
| list = separated_list(COMMA,record_field)  { list }

record_field:
| v=ID EQ e=exp             { (symbol(v), e) }

var_base:
| v= ID s = partSpecList { makeLvaluePartSpec ( SimpleVar (symbol v)^@ $startpos) $startpos s}

lvaluePartSpec:
| DOT i = ID              { FieldPart (symbol i )}
| LBRACK e = exp RBRACK   { SubscriptPart e}

partSpecList:
| s = list(lvaluePartSpec){s}

ty:
| s = ID                          { NameTy ((symbol s), $startpos) }
| LBRACE s= fielddataList RBRACE  { RecordTy s }
| ARRAY OF s= ID                  { ArrayTy ((symbol s), $startpos) }

fielddata:
| i1= ID COLON i2 = ID { Field { name = (symbol i1); escape = ref true; typ = ((symbol i2), $startpos(i2)); pos = $startpos(i2) }} 

tydecldata:
| TYPE i=ID EQ t=ty { Tdecl { name = (symbol i); ty=t; pos = $startpos(i) }}

symbolpos:
| COLON i = ID { (symbol i,$startpos) }

fundecldata:
FUNCTION i=ID LPAREN s=fielddataList RPAREN opt=option(symbolpos) EQ e=exp { Fdecl{ name = (symbol i); params = s; result = opt; body = e; pos = $startpos }}

decl:
| VAR i=ID opt = option(preceded(COLON, i = ID { (symbol i, $startpos) })) ASSIGN e=exp   { VarDec{ name= (symbol i); escape = ref true; typ= opt; init= e; pos= $startpos }}
| list = nonempty_list(fundecldata)                                                       { FunctionDec list }
| list = nonempty_list(tydecldata)                                                        { TypeDec list }

fielddataList:
| s= separated_list(COMMA,fielddata)  { s }

explist:
| s=separated_list(SEMICOLON,exp) { s }

arglist:
| s=separated_list(COMMA,exp) { s }

(* Top-level *)
program: e = exp EOF { e }

exp:
| e=exp_base  { e ^! $startpos }

var:
| var= var_base { var }