(*
 * parser by KINOSHITA Minoru
 * https://github.com/krtx/lua-parser
 * license: MIT
 *)
{
open Lexing
open Lua_syntax
open Lua_parser

let reserved_keywords =
  [ "and",      Lua_parser.AND
  ; "break",    Lua_parser.BREAK
  ; "do",       Lua_parser.DO
  ; "else",     Lua_parser.ELSE
  ; "elseif",   Lua_parser.ELSEIF
  ; "end",      Lua_parser.END
  ; "false",    Lua_parser.FALSE
  ; "for",      Lua_parser.FOR
  ; "function", Lua_parser.FUNCTION
  ; "goto",     Lua_parser.GOTO
  ; "if",       Lua_parser.IF
  ; "in",       Lua_parser.IN
  ; "local",    Lua_parser.LOCAL
  ; "nil",      Lua_parser.NIL
  ; "not",      Lua_parser.NOT
  ; "or",       Lua_parser.OR
  ; "repeat",   Lua_parser.REPEAT
  ; "return",   Lua_parser.RETURN
  ; "then",     Lua_parser.THEN
  ; "true",     Lua_parser.TRUE
  ; "until",    Lua_parser.UNTIL
  ; "while",    Lua_parser.WHILE
  ]

let next_line lexbuf =
  let pos = lexbuf.lex_curr_p in
  lexbuf.lex_curr_p <-
    { pos with pos_bol = lexbuf.lex_curr_pos;
               pos_lnum = pos.pos_lnum + 1
    }
}

let white = [' ' '\t']+
let newline = '\r' | '\n' | '\r' '\n'
let name = ['_' 'a'-'z' 'A'-'Z'] ['_' 'a'-'z' 'A'-'Z' '0'-'9']*
let hex = '0' ['x' 'X']

rule read = parse
  | '-' '-' '[' '[' { comment_long lexbuf }
  | '-' '-' { comment lexbuf }
  | white { read lexbuf }
  | newline { next_line lexbuf; read lexbuf }
  | name { let name = lexeme lexbuf in
           try
             List.assoc name reserved_keywords
           with
             Not_found -> Lua_parser.NAME name }
  | ['0'-'9']+ '.' ['0'-'9']+
      { Lua_parser.FLOAT (float_of_string (lexeme lexbuf)) }
  | ['0'-'9']+ ['e' 'E'] ['0'-'9']+
      { Lua_parser.FLOAT (float_of_string (lexeme lexbuf)) }
  | ['0'-'9']+ '.' ['0'-'9']* ['e' 'E'] ['0'-'9']+
      { Lua_parser.FLOAT (float_of_string (lexeme lexbuf)) }
  | ['0'-'9']+
      { Lua_parser.INTEGER (int_of_string (lexeme lexbuf)) }
  | hex ['0'-'9' 'A'-'F' 'a'-'f']+
      { Lua_parser.INTEGER (int_of_string (lexeme lexbuf)) }
  | ('\'' | '"') as delimiter
      { Lua_parser.LITERALSTRING
          (literal_string delimiter lexbuf) }
  | '[' '['
      { Lua_parser.LITERALSTRING
          (literal_string_long lexbuf) }
  | '=' { EQUAL }
  | ':' ':' { DOUBLECOLON }
  | ':' { COLON }
  | ';' { SEMICOLON }
  | ',' { COMMA }
  | '.' '.' '.' { TRIPLEDOT }
  | '.' '.' { DOUBLEDOT }
  | '.' { DOT }
  | '(' { LPAREN }
  | ')' { RPAREN }
  | '+' { PLUS }
  | '-' { HYPHEN }
  | '*' { ASTERISK }
  | '/' '/' { DOUBLESLASH }
  | '/' { SLASH }
  | '^' { HAT }
  | '%' { PERCENT }
  | '&' { AMPERSAND }
  | '~' { TILDA }
  | '|' { VERTICALBAR }
  | '>' '>' { DOUBLELT }
  | '<' '<' { DOUBLEGT }
  | '<' { GT }
  | '<' '=' { GTEQ }
  | '>' { LT }
  | '>' '=' { LTEQ }
  | '=' '=' { DOUBLEEQUAL }
  | '~' '=' { TILDAEQUAL }
  | '#' { SHARP }
  | '{' { LBRACE }
  | '}' { RBRACE }
  | '[' { LBRACKET }
  | ']' { RBRACKET }
  | eof { EOF }

and comment_long = parse
  | newline { next_line lexbuf; comment_long lexbuf }
  | ']' ']' { read lexbuf }
  | _ { comment_long lexbuf }

and comment = parse
  | newline { next_line lexbuf; read lexbuf }
  | _ { comment lexbuf }

and literal_string open_delimiter = parse
  | '\\' '\\'
      { "\\\\" ^ (literal_string open_delimiter lexbuf) }
  | '\\' '\''
      { "'" ^ (literal_string open_delimiter lexbuf) }
  | '\\' '"'
      { "\"" ^ (literal_string open_delimiter lexbuf) }
  | newline
      { next_line lexbuf; literal_string open_delimiter lexbuf }
  | _ as ch
      { if ch = open_delimiter
        then ""
        else (Char.escaped ch) ^ (literal_string open_delimiter lexbuf) }

and literal_string_long = parse
  | ']' ']' { "" }
  | newline { next_line lexbuf; literal_string_long lexbuf }
  | _ as ch { (Char.escaped ch) ^ (literal_string_long lexbuf) }
