%token LBRACK RBRACK
%token LPAR RPAR
%token LBRACE RBRACE
%token EOF
%token COLON DOT COMMA
%token ENDVER ENDFUNC ENDPROG
%token FUNCTION VERSION
%token PARAMS
%token ENTRY MAIN
%token <Ast.areg> REG
%token <Ast.alabel> LBL
%token <Ast.afun_id> FID
%token <Ast.acst> CSTI
%token LL RR
%token PLUS MINUS MULT GT LT GEQ LEQ EQ
%token UMINUS NEG ASSIGN
%token NOP MOVE CALL IRETURN COND PRINTEXPR PRINTSTRING FRAMESTATE ASSUME STORE LOAD FAIL
%token HINT HINTEQ
%token ARROW MEM
%token <string> MSG
%start <Ast.aprogram option> prog
%%

op:
  | r=REG {Ast.Areg r}
  | c=CSTI {Ast.Acsti c}

binop:
  | PLUS {Ast.Aplus}
  | MINUS {Ast.Aminus}
  | MULT {Ast.Amult}
  | GT {Ast.Agt}
  | LT {Ast.Alt}
  | GEQ {Ast.Ageq}
  | LEQ {Ast.Aleq}
  | EQ {Ast.Aeq}

unop:
  | UMINUS {Ast.Auminus}
  | NEG {Ast.Aneg}
  | ASSIGN {Ast.Aassign}

expr:
  | b=binop o1=op o2=op
    {Ast.Abinexpr (b,o1,o2)}
  | u=unop o=op
    {Ast.Aunexpr (u,o)}
  | o=op
    {Ast.Aunexpr (Ast.Aassign,o)}
  | LPAR e=expr RPAR
    {e}

list_expr:
  | {[]}
  | e=expr {[e]}
  | e=expr COMMA le=list_expr {e::le}

regexpr:
  | LPAR r=REG COMMA e=expr RPAR {(r,e)}

varmap:
  | {[]}
  | re=regexpr vm=varmap {re::vm}

movelist:
  | {[]}
  | re=regexpr ml=movelist {re::ml}

target:
  | f=FID DOT l=LBL
    { (f,l) }

synth:
  | t=target r=REG LBRACE vm=varmap RBRACE
    {(t,r,vm)}

list_synth:
  | {[]}
  | s=synth sl=list_synth {s::sl}

instruction:
  | NOP l=LBL
    {Ast.Anop (None,l)}
  | HINT r1=REG HINTEQ r2=REG l=LBL
    {Ast.Anop (Some (Ahint_eq(r1,r2)),l)}
  | HINT r=REG HINTEQ c=CSTI l=LBL
    {Ast.Anop (Some (Ahint_eq_val(r,c)),l)}
  | r=REG ARROW e=expr l=LBL
    {Ast.Aop (e,r,l)}
  | MOVE ml=movelist l=LBL
    {Ast.Amove (ml,l)}
  | r=REG ARROW CALL f=FID LPAR le=list_expr RPAR l=LBL
    {Ast.Acall (f,le,r,l)}
  | IRETURN e=expr
    {Ast.Aireturn e}
  | COND e=expr l1=LBL l2=LBL
    {Ast.Acond (e,l1,l2)}
  | STORE MEM LBRACK e2=expr RBRACK ARROW e1=expr l=LBL
    {Ast.Astore (e1,e2,l)}
  | r=REG ARROW LOAD MEM LBRACK e=expr RBRACK l=LBL
    {Ast.Aload (e,r,l)}
  | PRINTEXPR e=expr l=LBL
    {Ast.Aprintexpr (e,l)}
  | PRINTSTRING str=MSG l=LBL
    {Ast.Aprintstring (str,l)}
  | FRAMESTATE t=target LBRACE vm=varmap RBRACE LBRACK sl=list_synth RBRACK next=LBL
    { Ast.Aframestate (t,vm,sl,next) }
  | ASSUME LPAR el=list_expr RPAR t=target LBRACE vm=varmap RBRACE LBRACK sl=list_synth RBRACK next=LBL
    {Ast.Aassume (el,t,vm,sl,next)}
  | FAIL s=MSG
    {Ast.Afail (s)}

node:
  | LL l=LBL RR i=instruction
    {(l,i)}

list_node:
  | ENDVER {[]}
  | n=node ln=list_node {n::ln}

version_decl:
  | VERSION COLON LBRACK ENTRY COLON l=LBL RBRACK n=list_node
    {(l,n)}

list_reg:
  | {[]}
  | r=REG {[r]}
  | r=REG COMMA lr=list_reg {r::lr}

fun_decl:
  | FUNCTION f=FID COLON PARAMS COLON LPAR rl=list_reg RPAR v=version_decl ENDFUNC
    {(f,rl,v,None)}
  | FUNCTION f=FID COLON PARAMS COLON LPAR rl=list_reg RPAR v=version_decl vopt=version_decl ENDFUNC
    {(f,rl,v,Some vopt)}

list_fun:
  | ENDPROG {[]}
  | f=fun_decl lf=list_fun {f::lf}

prog:
  | LBRACK MAIN COLON f=FID RBRACK fl=list_fun {Some (f,fl)}
  | EOF {None}


%%
