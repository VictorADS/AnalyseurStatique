
module Basics = struct
  
  exception Error
  
  type token = 
    | TOK_int of (
# 56 "frontend/parser.mly"
       (string)
# 11 "frontend/parser.ml"
  )
    | TOK_id of (
# 55 "frontend/parser.mly"
       (string)
# 16 "frontend/parser.ml"
  )
    | TOK_WHILE
    | TOK_TRUE
    | TOK_STAR
    | TOK_SEMICOLON
    | TOK_RPAREN
    | TOK_RCURLY
    | TOK_RAND
    | TOK_PRINT
    | TOK_PLUS
    | TOK_NOT_EQUAL
    | TOK_MODULO
    | TOK_MINUS
    | TOK_LPAREN
    | TOK_LESS_EQUAL
    | TOK_LESS
    | TOK_LCURLY
    | TOK_INT
    | TOK_IF
    | TOK_HALT
    | TOK_GREATER_EQUAL
    | TOK_GREATER
    | TOK_FALSE
    | TOK_EXCLAIM
    | TOK_EQUAL_EQUAL
    | TOK_EQUAL
    | TOK_EOF
    | TOK_ELSE
    | TOK_DIVIDE
    | TOK_COMMA
    | TOK_BAR_BAR
    | TOK_ASSERT
    | TOK_AND_AND
  
end

include Basics

let _eRR =
  Basics.Error

type _menhir_env = {
  _menhir_lexer: Lexing.lexbuf -> token;
  _menhir_lexbuf: Lexing.lexbuf;
  _menhir_token: token;
  mutable _menhir_error: bool
}

and _menhir_state = 
  | MenhirState98
  | MenhirState94
  | MenhirState91
  | MenhirState86
  | MenhirState82
  | MenhirState80
  | MenhirState78
  | MenhirState73
  | MenhirState67
  | MenhirState65
  | MenhirState63
  | MenhirState60
  | MenhirState58
  | MenhirState52
  | MenhirState50
  | MenhirState48
  | MenhirState46
  | MenhirState44
  | MenhirState42
  | MenhirState40
  | MenhirState38
  | MenhirState36
  | MenhirState29
  | MenhirState27
  | MenhirState25
  | MenhirState23
  | MenhirState20
  | MenhirState18
  | MenhirState17
  | MenhirState16
  | MenhirState13
  | MenhirState6
  | MenhirState2
  | MenhirState0

# 15 "frontend/parser.mly"
  
open Abstract_syntax_tree

# 105 "frontend/parser.ml"

let rec _menhir_run42 : _menhir_env -> 'ttv_tail * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | TOK_LPAREN ->
        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState42 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_MINUS ->
        _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState42 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_PLUS ->
        _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState42 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_RAND ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState42 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_id _v ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState42 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_int _v ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState42 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState42

and _menhir_run44 : _menhir_env -> 'ttv_tail * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | TOK_LPAREN ->
        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState44 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_MINUS ->
        _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState44 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_PLUS ->
        _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState44 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_RAND ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState44 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_id _v ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState44 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_int _v ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState44 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState44

and _menhir_run46 : _menhir_env -> 'ttv_tail * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | TOK_LPAREN ->
        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState46 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_MINUS ->
        _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState46 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_PLUS ->
        _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState46 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_RAND ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState46 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_id _v ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState46 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_int _v ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState46 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState46

and _menhir_run48 : _menhir_env -> 'ttv_tail * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | TOK_LPAREN ->
        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState48 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_MINUS ->
        _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState48 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_PLUS ->
        _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState48 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_RAND ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState48 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_id _v ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState48 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_int _v ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState48 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState48

and _menhir_run50 : _menhir_env -> 'ttv_tail * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | TOK_LPAREN ->
        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState50 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_MINUS ->
        _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState50 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_PLUS ->
        _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState50 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_RAND ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState50 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_id _v ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState50 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_int _v ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState50 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState50

and _menhir_run52 : _menhir_env -> 'ttv_tail * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | TOK_LPAREN ->
        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState52 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_MINUS ->
        _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState52 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_PLUS ->
        _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState52 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_RAND ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState52 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_id _v ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState52 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_int _v ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState52 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState52

and _menhir_run20 : _menhir_env -> 'ttv_tail * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | TOK_LPAREN ->
        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState20 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_MINUS ->
        _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState20 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_PLUS ->
        _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState20 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_RAND ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState20 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_id _v ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState20 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_int _v ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState20 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState20

and _menhir_run22 : _menhir_env -> ('ttv_tail * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos ->
    let _menhir_env = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : ('freshtv379 * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position) = Obj.magic _menhir_stack in
    let (_endpos__3_ : Lexing.position) = _endpos in
    ((let ((_menhir_stack, _menhir_s, _startpos__1_), _endpos_e_, _, (e : 'tv_int_expr), _startpos_e_) = _menhir_stack in
    let _3 = () in
    let _1 = () in
    let _startpos = _startpos__1_ in
    let _endpos = _endpos__3_ in
    let _v : 'tv_int_expr = 
# 143 "frontend/parser.mly"
    ( e )
# 275 "frontend/parser.ml"
     in
    _menhir_goto_int_expr _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv380)

and _menhir_run23 : _menhir_env -> 'ttv_tail * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _startpos ->
    let _menhir_stack = (_menhir_stack, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | TOK_LPAREN ->
        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState23 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_MINUS ->
        _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState23 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_PLUS ->
        _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState23 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_RAND ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState23 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_id _v ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState23 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_int _v ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState23 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState23

and _menhir_run25 : _menhir_env -> 'ttv_tail * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | TOK_LPAREN ->
        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState25 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_MINUS ->
        _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState25 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_PLUS ->
        _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState25 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_RAND ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState25 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_id _v ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState25 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_int _v ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState25 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState25

and _menhir_run29 : _menhir_env -> 'ttv_tail * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _startpos ->
    let _menhir_stack = (_menhir_stack, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | TOK_LPAREN ->
        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState29 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_MINUS ->
        _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState29 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_PLUS ->
        _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState29 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_RAND ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState29 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_id _v ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState29 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_int _v ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState29 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState29

and _menhir_run27 : _menhir_env -> 'ttv_tail * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | TOK_LPAREN ->
        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState27 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_MINUS ->
        _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState27 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_PLUS ->
        _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState27 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_RAND ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState27 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_id _v ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState27 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_int _v ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState27 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState27

and _menhir_goto_sign_int_literal : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> 'tv_sign_int_literal -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    let _menhir_stack = (_menhir_stack, _endpos, _menhir_s, _v, _startpos) in
    match _menhir_s with
    | MenhirState6 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv369 * _menhir_state * Lexing.position) * Lexing.position) * Lexing.position * _menhir_state * 'tv_sign_int_literal * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | TOK_COMMA ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv365 * _menhir_state * Lexing.position) * Lexing.position) * Lexing.position * _menhir_state * 'tv_sign_int_literal * Lexing.position) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | TOK_MINUS ->
                _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState13 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TOK_PLUS ->
                _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState13 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TOK_int _v ->
                _menhir_run7 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState13 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState13) : 'freshtv366)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv367 * _menhir_state * Lexing.position) * Lexing.position) * Lexing.position * _menhir_state * 'tv_sign_int_literal * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv368)) : 'freshtv370)
    | MenhirState13 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (((('freshtv377 * _menhir_state * Lexing.position) * Lexing.position) * Lexing.position * _menhir_state * 'tv_sign_int_literal * Lexing.position)) * Lexing.position * _menhir_state * 'tv_sign_int_literal * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | TOK_RPAREN ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (((('freshtv373 * _menhir_state * Lexing.position) * Lexing.position) * Lexing.position * _menhir_state * 'tv_sign_int_literal * Lexing.position)) * Lexing.position * _menhir_state * 'tv_sign_int_literal * Lexing.position) = Obj.magic _menhir_stack in
            let (_endpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (((('freshtv371 * _menhir_state * Lexing.position) * Lexing.position) * Lexing.position * _menhir_state * 'tv_sign_int_literal * Lexing.position)) * Lexing.position * _menhir_state * 'tv_sign_int_literal * Lexing.position) = Obj.magic _menhir_stack in
            let (_endpos__6_ : Lexing.position) = _endpos in
            ((let ((((_menhir_stack, _menhir_s, _startpos__1_), _startpos__2_), _endpos_x0_, _, (x0 : 'tv_sign_int_literal), _startpos_x0_), _endpos_x1_, _, (x1 : 'tv_sign_int_literal), _startpos_x1_) = _menhir_stack in
            let _6 = () in
            let _4 = () in
            let _2 = () in
            let _1 = () in
            let _startpos = _startpos__1_ in
            let _endpos = _endpos__6_ in
            let _v : 'tv_int_expr = let e2 =
              let _endpos_x_ = _endpos_x1_ in
              let _startpos_x_ = _startpos_x1_ in
              let x = x1 in
              let _endpos = _endpos_x_ in
              let _startpos = _startpos_x_ in
              
# 217 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 432 "frontend/parser.ml"
              
            in
            let e1 =
              let _endpos_x_ = _endpos_x0_ in
              let _startpos_x_ = _startpos_x0_ in
              let x = x0 in
              let _endpos = _endpos_x_ in
              let _startpos = _startpos_x_ in
              
# 217 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 444 "frontend/parser.ml"
              
            in
            
# 159 "frontend/parser.mly"
    ( AST_rand (e1, e2) )
# 450 "frontend/parser.ml"
             in
            _menhir_goto_int_expr _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv372)) : 'freshtv374)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (((('freshtv375 * _menhir_state * Lexing.position) * Lexing.position) * Lexing.position * _menhir_state * 'tv_sign_int_literal * Lexing.position)) * Lexing.position * _menhir_state * 'tv_sign_int_literal * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv376)) : 'freshtv378)
    | _ ->
        _menhir_fail ()

and _menhir_run58 : _menhir_env -> 'ttv_tail * Lexing.position * _menhir_state * 'tv_bool_expr * Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | TOK_EXCLAIM ->
        _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState58 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_FALSE ->
        _menhir_run39 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState58 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_LPAREN ->
        _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState58 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_MINUS ->
        _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState58 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_PLUS ->
        _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState58 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_RAND ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState58 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_TRUE ->
        _menhir_run37 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState58 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_id _v ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState58 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_int _v ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState58 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState58

and _menhir_run60 : _menhir_env -> 'ttv_tail * Lexing.position * _menhir_state * 'tv_bool_expr * Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | TOK_EXCLAIM ->
        _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState60 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_FALSE ->
        _menhir_run39 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState60 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_LPAREN ->
        _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState60 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_MINUS ->
        _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState60 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_PLUS ->
        _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState60 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_RAND ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState60 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_TRUE ->
        _menhir_run37 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState60 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_id _v ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState60 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_int _v ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState60 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState60

and _menhir_goto_separated_nonempty_list_TOK_COMMA_ext_TOK_id__ : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_separated_nonempty_list_TOK_COMMA_ext_TOK_id__ -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    match _menhir_s with
    | MenhirState67 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv359 * Lexing.position * _menhir_state * (
# 55 "frontend/parser.mly"
       (string)
# 527 "frontend/parser.ml"
        ) * Lexing.position)) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : 'tv_separated_nonempty_list_TOK_COMMA_ext_TOK_id__) = _v in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv357 * Lexing.position * _menhir_state * (
# 55 "frontend/parser.mly"
       (string)
# 535 "frontend/parser.ml"
        ) * Lexing.position)) = Obj.magic _menhir_stack in
        let (_ : _menhir_state) = _menhir_s in
        let ((xs : 'tv_separated_nonempty_list_TOK_COMMA_ext_TOK_id__) : 'tv_separated_nonempty_list_TOK_COMMA_ext_TOK_id__) = _v in
        ((let (_menhir_stack, _endpos_x0_, _menhir_s, (x0 : (
# 55 "frontend/parser.mly"
       (string)
# 542 "frontend/parser.ml"
        )), _startpos_x0_) = _menhir_stack in
        let _2 = () in
        let _v : 'tv_separated_nonempty_list_TOK_COMMA_ext_TOK_id__ = let x =
          let _endpos_x_ = _endpos_x0_ in
          let _startpos_x_ = _startpos_x0_ in
          let x = x0 in
          let _endpos = _endpos_x_ in
          let _startpos = _startpos_x_ in
          
# 217 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 554 "frontend/parser.ml"
          
        in
        
# 218 "/home/tas/.opam/system/lib/menhir/standard.mly"
    ( x :: xs )
# 560 "frontend/parser.ml"
         in
        _menhir_goto_separated_nonempty_list_TOK_COMMA_ext_TOK_id__ _menhir_env _menhir_stack _menhir_s _v) : 'freshtv358)) : 'freshtv360)
    | MenhirState65 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv363) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : 'tv_separated_nonempty_list_TOK_COMMA_ext_TOK_id__) = _v in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv361) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let ((x : 'tv_separated_nonempty_list_TOK_COMMA_ext_TOK_id__) : 'tv_separated_nonempty_list_TOK_COMMA_ext_TOK_id__) = _v in
        ((let _v : 'tv_loption_separated_nonempty_list_TOK_COMMA_ext_TOK_id___ = 
# 131 "/home/tas/.opam/system/lib/menhir/standard.mly"
    ( x )
# 575 "frontend/parser.ml"
         in
        _menhir_goto_loption_separated_nonempty_list_TOK_COMMA_ext_TOK_id___ _menhir_env _menhir_stack _menhir_s _v) : 'freshtv362)) : 'freshtv364)
    | _ ->
        _menhir_fail ()

and _menhir_goto_list_ext_decl__ : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_list_ext_decl__ -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState73 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv351 * _menhir_state * Lexing.position) * _menhir_state * 'tv_list_ext_decl__) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | TOK_ASSERT ->
            _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState78 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_HALT ->
            _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState78 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_IF ->
            _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState78 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_LCURLY ->
            _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState78 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_PRINT ->
            _menhir_run64 _menhir_env (Obj.magic _menhir_stack) MenhirState78 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_WHILE ->
            _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState78 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_id _v ->
            _menhir_run1 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState78 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_RCURLY ->
            _menhir_reduce29 _menhir_env (Obj.magic _menhir_stack) MenhirState78
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState78) : 'freshtv352)
    | MenhirState98 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv355 * Lexing.position * _menhir_state * 'tv_decl * Lexing.position) * _menhir_state * 'tv_list_ext_decl__) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv353 * Lexing.position * _menhir_state * 'tv_decl * Lexing.position) * _menhir_state * 'tv_list_ext_decl__) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _endpos_x0_, _menhir_s, (x0 : 'tv_decl), _startpos_x0_), _, (xs : 'tv_list_ext_decl__)) = _menhir_stack in
        let _v : 'tv_list_ext_decl__ = let x =
          let _endpos_x_ = _endpos_x0_ in
          let _startpos_x_ = _startpos_x0_ in
          let x = x0 in
          let _endpos = _endpos_x_ in
          let _startpos = _startpos_x_ in
          
# 217 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 626 "frontend/parser.ml"
          
        in
        
# 188 "/home/tas/.opam/system/lib/menhir/standard.mly"
    ( x :: xs )
# 632 "frontend/parser.ml"
         in
        _menhir_goto_list_ext_decl__ _menhir_env _menhir_stack _menhir_s _v) : 'freshtv354)) : 'freshtv356)
    | _ ->
        _menhir_fail ()

and _menhir_fail : unit -> 'a =
  fun () ->
    Printf.fprintf Pervasives.stderr "Internal failure -- please contact the parser generator's developers.\n%!";
    assert false

and _menhir_goto_int_expr : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> 'tv_int_expr -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    let _menhir_stack = (_menhir_stack, _endpos, _menhir_s, _v, _startpos) in
    match _menhir_s with
    | MenhirState18 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv261 * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | TOK_DIVIDE ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack)
        | TOK_MINUS ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_MODULO ->
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack)
        | TOK_PLUS ->
            _menhir_run23 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_RPAREN ->
            _menhir_run22 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p
        | TOK_STAR ->
            _menhir_run20 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv259 * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv260)) : 'freshtv262)
    | MenhirState20 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv265 * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position)) * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv263 * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position)) * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _endpos_x0_, _menhir_s, (x0 : 'tv_int_expr), _startpos_x0_), _endpos_x1_, _, (x1 : 'tv_int_expr), _startpos_x1_) = _menhir_stack in
        let _10 = () in
        let _startpos = _startpos_x0_ in
        let _endpos = _endpos_x1_ in
        let _v : 'tv_int_expr = let e2 =
          let _endpos_x_ = _endpos_x1_ in
          let _startpos_x_ = _startpos_x1_ in
          let x = x1 in
          let _endpos = _endpos_x_ in
          let _startpos = _startpos_x_ in
          
# 217 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 690 "frontend/parser.ml"
          
        in
        let o =
          let _1 = _10 in
          
# 98 "frontend/parser.mly"
                     ( AST_MULTIPLY )
# 698 "frontend/parser.ml"
          
        in
        let e1 =
          let _endpos_x_ = _endpos_x0_ in
          let _startpos_x_ = _startpos_x0_ in
          let x = x0 in
          let _endpos = _endpos_x_ in
          let _startpos = _startpos_x_ in
          
# 217 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 710 "frontend/parser.ml"
          
        in
        
# 155 "frontend/parser.mly"
    ( AST_int_binary (o,e1,e2) )
# 716 "frontend/parser.ml"
         in
        _menhir_goto_int_expr _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv264)) : 'freshtv266)
    | MenhirState23 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv271 * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position) * Lexing.position) * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | TOK_DIVIDE ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack)
        | TOK_MODULO ->
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack)
        | TOK_STAR ->
            _menhir_run20 _menhir_env (Obj.magic _menhir_stack)
        | TOK_AND_AND | TOK_BAR_BAR | TOK_EQUAL_EQUAL | TOK_GREATER | TOK_GREATER_EQUAL | TOK_LESS | TOK_LESS_EQUAL | TOK_MINUS | TOK_NOT_EQUAL | TOK_PLUS | TOK_RPAREN | TOK_SEMICOLON ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv267 * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position) * Lexing.position) * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position) = Obj.magic _menhir_stack in
            ((let (((_menhir_stack, _endpos_x0_, _menhir_s, (x0 : 'tv_int_expr), _startpos_x0_), _startpos__10_), _endpos_x1_, _, (x1 : 'tv_int_expr), _startpos_x1_) = _menhir_stack in
            let _10 = () in
            let _startpos = _startpos_x0_ in
            let _endpos = _endpos_x1_ in
            let _v : 'tv_int_expr = let e2 =
              let _endpos_x_ = _endpos_x1_ in
              let _startpos_x_ = _startpos_x1_ in
              let x = x1 in
              let _endpos = _endpos_x_ in
              let _startpos = _startpos_x_ in
              
# 217 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 747 "frontend/parser.ml"
              
            in
            let o =
              let _1 = _10 in
              
# 100 "frontend/parser.mly"
                     ( AST_PLUS )
# 755 "frontend/parser.ml"
              
            in
            let e1 =
              let _endpos_x_ = _endpos_x0_ in
              let _startpos_x_ = _startpos_x0_ in
              let x = x0 in
              let _endpos = _endpos_x_ in
              let _startpos = _startpos_x_ in
              
# 217 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 767 "frontend/parser.ml"
              
            in
            
# 155 "frontend/parser.mly"
    ( AST_int_binary (o,e1,e2) )
# 773 "frontend/parser.ml"
             in
            _menhir_goto_int_expr _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv268)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv269 * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position) * Lexing.position) * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv270)) : 'freshtv272)
    | MenhirState25 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv275 * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position)) * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv273 * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position)) * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _endpos_x0_, _menhir_s, (x0 : 'tv_int_expr), _startpos_x0_), _endpos_x1_, _, (x1 : 'tv_int_expr), _startpos_x1_) = _menhir_stack in
        let _10 = () in
        let _startpos = _startpos_x0_ in
        let _endpos = _endpos_x1_ in
        let _v : 'tv_int_expr = let e2 =
          let _endpos_x_ = _endpos_x1_ in
          let _startpos_x_ = _startpos_x1_ in
          let x = x1 in
          let _endpos = _endpos_x_ in
          let _startpos = _startpos_x_ in
          
# 217 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 801 "frontend/parser.ml"
          
        in
        let o =
          let _1 = _10 in
          
# 102 "frontend/parser.mly"
                  ( AST_MODULO )
# 809 "frontend/parser.ml"
          
        in
        let e1 =
          let _endpos_x_ = _endpos_x0_ in
          let _startpos_x_ = _startpos_x0_ in
          let x = x0 in
          let _endpos = _endpos_x_ in
          let _startpos = _startpos_x_ in
          
# 217 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 821 "frontend/parser.ml"
          
        in
        
# 155 "frontend/parser.mly"
    ( AST_int_binary (o,e1,e2) )
# 827 "frontend/parser.ml"
         in
        _menhir_goto_int_expr _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv274)) : 'freshtv276)
    | MenhirState27 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv279 * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position)) * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv277 * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position)) * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _endpos_x0_, _menhir_s, (x0 : 'tv_int_expr), _startpos_x0_), _endpos_x1_, _, (x1 : 'tv_int_expr), _startpos_x1_) = _menhir_stack in
        let _10 = () in
        let _startpos = _startpos_x0_ in
        let _endpos = _endpos_x1_ in
        let _v : 'tv_int_expr = let e2 =
          let _endpos_x_ = _endpos_x1_ in
          let _startpos_x_ = _startpos_x1_ in
          let x = x1 in
          let _endpos = _endpos_x_ in
          let _startpos = _startpos_x_ in
          
# 217 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 848 "frontend/parser.ml"
          
        in
        let o =
          let _1 = _10 in
          
# 99 "frontend/parser.mly"
                     ( AST_DIVIDE )
# 856 "frontend/parser.ml"
          
        in
        let e1 =
          let _endpos_x_ = _endpos_x0_ in
          let _startpos_x_ = _startpos_x0_ in
          let x = x0 in
          let _endpos = _endpos_x_ in
          let _startpos = _startpos_x_ in
          
# 217 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 868 "frontend/parser.ml"
          
        in
        
# 155 "frontend/parser.mly"
    ( AST_int_binary (o,e1,e2) )
# 874 "frontend/parser.ml"
         in
        _menhir_goto_int_expr _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv278)) : 'freshtv280)
    | MenhirState29 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv285 * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position) * Lexing.position) * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | TOK_DIVIDE ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack)
        | TOK_MODULO ->
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack)
        | TOK_STAR ->
            _menhir_run20 _menhir_env (Obj.magic _menhir_stack)
        | TOK_AND_AND | TOK_BAR_BAR | TOK_EQUAL_EQUAL | TOK_GREATER | TOK_GREATER_EQUAL | TOK_LESS | TOK_LESS_EQUAL | TOK_MINUS | TOK_NOT_EQUAL | TOK_PLUS | TOK_RPAREN | TOK_SEMICOLON ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv281 * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position) * Lexing.position) * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position) = Obj.magic _menhir_stack in
            ((let (((_menhir_stack, _endpos_x0_, _menhir_s, (x0 : 'tv_int_expr), _startpos_x0_), _startpos__10_), _endpos_x1_, _, (x1 : 'tv_int_expr), _startpos_x1_) = _menhir_stack in
            let _10 = () in
            let _startpos = _startpos_x0_ in
            let _endpos = _endpos_x1_ in
            let _v : 'tv_int_expr = let e2 =
              let _endpos_x_ = _endpos_x1_ in
              let _startpos_x_ = _startpos_x1_ in
              let x = x1 in
              let _endpos = _endpos_x_ in
              let _startpos = _startpos_x_ in
              
# 217 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 905 "frontend/parser.ml"
              
            in
            let o =
              let _1 = _10 in
              
# 101 "frontend/parser.mly"
                     ( AST_MINUS )
# 913 "frontend/parser.ml"
              
            in
            let e1 =
              let _endpos_x_ = _endpos_x0_ in
              let _startpos_x_ = _startpos_x0_ in
              let x = x0 in
              let _endpos = _endpos_x_ in
              let _startpos = _startpos_x_ in
              
# 217 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 925 "frontend/parser.ml"
              
            in
            
# 155 "frontend/parser.mly"
    ( AST_int_binary (o,e1,e2) )
# 931 "frontend/parser.ml"
             in
            _menhir_goto_int_expr _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv282)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv283 * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position) * Lexing.position) * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv284)) : 'freshtv286)
    | MenhirState17 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv291 * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | TOK_DIVIDE ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack)
        | TOK_MODULO ->
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack)
        | TOK_STAR ->
            _menhir_run20 _menhir_env (Obj.magic _menhir_stack)
        | TOK_AND_AND | TOK_BAR_BAR | TOK_EQUAL_EQUAL | TOK_GREATER | TOK_GREATER_EQUAL | TOK_LESS | TOK_LESS_EQUAL | TOK_MINUS | TOK_NOT_EQUAL | TOK_PLUS | TOK_RPAREN | TOK_SEMICOLON ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv287 * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position) = Obj.magic _menhir_stack in
            ((let ((_menhir_stack, _menhir_s, _startpos__10_), _endpos_x0_, _, (x0 : 'tv_int_expr), _startpos_x0_) = _menhir_stack in
            let _10 = () in
            let _startpos = _startpos__10_ in
            let _endpos = _endpos_x0_ in
            let _v : 'tv_int_expr = let e =
              let _endpos_x_ = _endpos_x0_ in
              let _startpos_x_ = _startpos_x0_ in
              let x = x0 in
              let _endpos = _endpos_x_ in
              let _startpos = _startpos_x_ in
              
# 217 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 969 "frontend/parser.ml"
              
            in
            let o =
              let _1 = _10 in
              
# 90 "frontend/parser.mly"
                     ( AST_UNARY_MINUS )
# 977 "frontend/parser.ml"
              
            in
            
# 152 "frontend/parser.mly"
    ( AST_int_unary (o,e) )
# 983 "frontend/parser.ml"
             in
            _menhir_goto_int_expr _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv288)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv289 * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv290)) : 'freshtv292)
    | MenhirState16 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv297 * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | TOK_DIVIDE ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack)
        | TOK_MODULO ->
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack)
        | TOK_STAR ->
            _menhir_run20 _menhir_env (Obj.magic _menhir_stack)
        | TOK_AND_AND | TOK_BAR_BAR | TOK_EQUAL_EQUAL | TOK_GREATER | TOK_GREATER_EQUAL | TOK_LESS | TOK_LESS_EQUAL | TOK_MINUS | TOK_NOT_EQUAL | TOK_PLUS | TOK_RPAREN | TOK_SEMICOLON ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv293 * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position) = Obj.magic _menhir_stack in
            ((let ((_menhir_stack, _menhir_s, _startpos__10_), _endpos_x0_, _, (x0 : 'tv_int_expr), _startpos_x0_) = _menhir_stack in
            let _10 = () in
            let _startpos = _startpos__10_ in
            let _endpos = _endpos_x0_ in
            let _v : 'tv_int_expr = let e =
              let _endpos_x_ = _endpos_x0_ in
              let _startpos_x_ = _startpos_x0_ in
              let x = x0 in
              let _endpos = _endpos_x_ in
              let _startpos = _startpos_x_ in
              
# 217 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 1021 "frontend/parser.ml"
              
            in
            let o =
              let _1 = _10 in
              
# 89 "frontend/parser.mly"
                     ( AST_UNARY_PLUS )
# 1029 "frontend/parser.ml"
              
            in
            
# 152 "frontend/parser.mly"
    ( AST_int_unary (o,e) )
# 1035 "frontend/parser.ml"
             in
            _menhir_goto_int_expr _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv294)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv295 * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv296)) : 'freshtv298)
    | MenhirState2 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv305 * Lexing.position * _menhir_state * (
# 55 "frontend/parser.mly"
       (string)
# 1050 "frontend/parser.ml"
        ) * Lexing.position)) * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | TOK_DIVIDE ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack)
        | TOK_MINUS ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_MODULO ->
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack)
        | TOK_PLUS ->
            _menhir_run23 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_SEMICOLON ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv301 * Lexing.position * _menhir_state * (
# 55 "frontend/parser.mly"
       (string)
# 1068 "frontend/parser.ml"
            ) * Lexing.position)) * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position) = Obj.magic _menhir_stack in
            let (_endpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv299 * Lexing.position * _menhir_state * (
# 55 "frontend/parser.mly"
       (string)
# 1076 "frontend/parser.ml"
            ) * Lexing.position)) * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position) = Obj.magic _menhir_stack in
            let (_endpos__4_ : Lexing.position) = _endpos in
            ((let ((_menhir_stack, _endpos_x0_, _menhir_s, (x0 : (
# 55 "frontend/parser.mly"
       (string)
# 1082 "frontend/parser.ml"
            )), _startpos_x0_), _endpos_x1_, _, (x1 : 'tv_int_expr), _startpos_x1_) = _menhir_stack in
            let _4 = () in
            let _2 = () in
            let _startpos = _startpos_x0_ in
            let _endpos = _endpos__4_ in
            let _v : 'tv_stat = let f =
              let _endpos_x_ = _endpos_x1_ in
              let _startpos_x_ = _startpos_x1_ in
              let x = x1 in
              let _endpos = _endpos_x_ in
              let _startpos = _startpos_x_ in
              
# 217 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 1097 "frontend/parser.ml"
              
            in
            let e =
              let _endpos_x_ = _endpos_x0_ in
              let _startpos_x_ = _startpos_x0_ in
              let x = x0 in
              let _endpos = _endpos_x_ in
              let _startpos = _startpos_x_ in
              
# 217 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 1109 "frontend/parser.ml"
              
            in
            
# 191 "frontend/parser.mly"
  ( AST_assign (e, f) )
# 1115 "frontend/parser.ml"
             in
            _menhir_goto_stat _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv300)) : 'freshtv302)
        | TOK_STAR ->
            _menhir_run20 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv303 * Lexing.position * _menhir_state * (
# 55 "frontend/parser.mly"
       (string)
# 1127 "frontend/parser.ml"
            ) * Lexing.position)) * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv304)) : 'freshtv306)
    | MenhirState86 | MenhirState80 | MenhirState36 | MenhirState60 | MenhirState58 | MenhirState40 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv309 * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | TOK_DIVIDE ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack)
        | TOK_EQUAL_EQUAL ->
            _menhir_run52 _menhir_env (Obj.magic _menhir_stack)
        | TOK_GREATER ->
            _menhir_run50 _menhir_env (Obj.magic _menhir_stack)
        | TOK_GREATER_EQUAL ->
            _menhir_run48 _menhir_env (Obj.magic _menhir_stack)
        | TOK_LESS ->
            _menhir_run46 _menhir_env (Obj.magic _menhir_stack)
        | TOK_LESS_EQUAL ->
            _menhir_run44 _menhir_env (Obj.magic _menhir_stack)
        | TOK_MINUS ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_MODULO ->
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack)
        | TOK_NOT_EQUAL ->
            _menhir_run42 _menhir_env (Obj.magic _menhir_stack)
        | TOK_PLUS ->
            _menhir_run23 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_STAR ->
            _menhir_run20 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv307 * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv308)) : 'freshtv310)
    | MenhirState42 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv315 * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position)) * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | TOK_DIVIDE ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack)
        | TOK_MINUS ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_MODULO ->
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack)
        | TOK_PLUS ->
            _menhir_run23 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_STAR ->
            _menhir_run20 _menhir_env (Obj.magic _menhir_stack)
        | TOK_AND_AND | TOK_BAR_BAR | TOK_RPAREN ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv311 * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position)) * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position) = Obj.magic _menhir_stack in
            ((let ((_menhir_stack, _endpos_x0_, _menhir_s, (x0 : 'tv_int_expr), _startpos_x0_), _endpos_x1_, _, (x1 : 'tv_int_expr), _startpos_x1_) = _menhir_stack in
            let _10 = () in
            let _startpos = _startpos_x0_ in
            let _endpos = _endpos_x1_ in
            let _v : 'tv_bool_expr = let e2 =
              let _endpos_x_ = _endpos_x1_ in
              let _startpos_x_ = _startpos_x1_ in
              let x = x1 in
              let _endpos = _endpos_x_ in
              let _startpos = _startpos_x_ in
              
# 217 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 1198 "frontend/parser.ml"
              
            in
            let o =
              let _1 = _10 in
              
# 111 "frontend/parser.mly"
                     ( AST_NOT_EQUAL )
# 1206 "frontend/parser.ml"
              
            in
            let e1 =
              let _endpos_x_ = _endpos_x0_ in
              let _startpos_x_ = _startpos_x0_ in
              let x = x0 in
              let _endpos = _endpos_x_ in
              let _startpos = _startpos_x_ in
              
# 217 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 1218 "frontend/parser.ml"
              
            in
            
# 137 "frontend/parser.mly"
    ( AST_compare (o,e1,e2) )
# 1224 "frontend/parser.ml"
             in
            _menhir_goto_bool_expr _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv312)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv313 * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position)) * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv314)) : 'freshtv316)
    | MenhirState44 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv321 * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position)) * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | TOK_DIVIDE ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack)
        | TOK_MINUS ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_MODULO ->
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack)
        | TOK_PLUS ->
            _menhir_run23 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_STAR ->
            _menhir_run20 _menhir_env (Obj.magic _menhir_stack)
        | TOK_AND_AND | TOK_BAR_BAR | TOK_RPAREN ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv317 * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position)) * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position) = Obj.magic _menhir_stack in
            ((let ((_menhir_stack, _endpos_x0_, _menhir_s, (x0 : 'tv_int_expr), _startpos_x0_), _endpos_x1_, _, (x1 : 'tv_int_expr), _startpos_x1_) = _menhir_stack in
            let _10 = () in
            let _startpos = _startpos_x0_ in
            let _endpos = _endpos_x1_ in
            let _v : 'tv_bool_expr = let e2 =
              let _endpos_x_ = _endpos_x1_ in
              let _startpos_x_ = _startpos_x1_ in
              let x = x1 in
              let _endpos = _endpos_x_ in
              let _startpos = _startpos_x_ in
              
# 217 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 1266 "frontend/parser.ml"
              
            in
            let o =
              let _1 = _10 in
              
# 108 "frontend/parser.mly"
                     ( AST_LESS_EQUAL )
# 1274 "frontend/parser.ml"
              
            in
            let e1 =
              let _endpos_x_ = _endpos_x0_ in
              let _startpos_x_ = _startpos_x0_ in
              let x = x0 in
              let _endpos = _endpos_x_ in
              let _startpos = _startpos_x_ in
              
# 217 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 1286 "frontend/parser.ml"
              
            in
            
# 137 "frontend/parser.mly"
    ( AST_compare (o,e1,e2) )
# 1292 "frontend/parser.ml"
             in
            _menhir_goto_bool_expr _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv318)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv319 * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position)) * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv320)) : 'freshtv322)
    | MenhirState46 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv327 * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position)) * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | TOK_DIVIDE ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack)
        | TOK_MINUS ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_MODULO ->
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack)
        | TOK_PLUS ->
            _menhir_run23 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_STAR ->
            _menhir_run20 _menhir_env (Obj.magic _menhir_stack)
        | TOK_AND_AND | TOK_BAR_BAR | TOK_RPAREN ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv323 * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position)) * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position) = Obj.magic _menhir_stack in
            ((let ((_menhir_stack, _endpos_x0_, _menhir_s, (x0 : 'tv_int_expr), _startpos_x0_), _endpos_x1_, _, (x1 : 'tv_int_expr), _startpos_x1_) = _menhir_stack in
            let _10 = () in
            let _startpos = _startpos_x0_ in
            let _endpos = _endpos_x1_ in
            let _v : 'tv_bool_expr = let e2 =
              let _endpos_x_ = _endpos_x1_ in
              let _startpos_x_ = _startpos_x1_ in
              let x = x1 in
              let _endpos = _endpos_x_ in
              let _startpos = _startpos_x_ in
              
# 217 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 1334 "frontend/parser.ml"
              
            in
            let o =
              let _1 = _10 in
              
# 106 "frontend/parser.mly"
                     ( AST_LESS )
# 1342 "frontend/parser.ml"
              
            in
            let e1 =
              let _endpos_x_ = _endpos_x0_ in
              let _startpos_x_ = _startpos_x0_ in
              let x = x0 in
              let _endpos = _endpos_x_ in
              let _startpos = _startpos_x_ in
              
# 217 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 1354 "frontend/parser.ml"
              
            in
            
# 137 "frontend/parser.mly"
    ( AST_compare (o,e1,e2) )
# 1360 "frontend/parser.ml"
             in
            _menhir_goto_bool_expr _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv324)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv325 * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position)) * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv326)) : 'freshtv328)
    | MenhirState48 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv333 * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position)) * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | TOK_DIVIDE ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack)
        | TOK_MINUS ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_MODULO ->
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack)
        | TOK_PLUS ->
            _menhir_run23 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_STAR ->
            _menhir_run20 _menhir_env (Obj.magic _menhir_stack)
        | TOK_AND_AND | TOK_BAR_BAR | TOK_RPAREN ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv329 * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position)) * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position) = Obj.magic _menhir_stack in
            ((let ((_menhir_stack, _endpos_x0_, _menhir_s, (x0 : 'tv_int_expr), _startpos_x0_), _endpos_x1_, _, (x1 : 'tv_int_expr), _startpos_x1_) = _menhir_stack in
            let _10 = () in
            let _startpos = _startpos_x0_ in
            let _endpos = _endpos_x1_ in
            let _v : 'tv_bool_expr = let e2 =
              let _endpos_x_ = _endpos_x1_ in
              let _startpos_x_ = _startpos_x1_ in
              let x = x1 in
              let _endpos = _endpos_x_ in
              let _startpos = _startpos_x_ in
              
# 217 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 1402 "frontend/parser.ml"
              
            in
            let o =
              let _1 = _10 in
              
# 109 "frontend/parser.mly"
                     ( AST_GREATER_EQUAL )
# 1410 "frontend/parser.ml"
              
            in
            let e1 =
              let _endpos_x_ = _endpos_x0_ in
              let _startpos_x_ = _startpos_x0_ in
              let x = x0 in
              let _endpos = _endpos_x_ in
              let _startpos = _startpos_x_ in
              
# 217 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 1422 "frontend/parser.ml"
              
            in
            
# 137 "frontend/parser.mly"
    ( AST_compare (o,e1,e2) )
# 1428 "frontend/parser.ml"
             in
            _menhir_goto_bool_expr _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv330)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv331 * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position)) * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv332)) : 'freshtv334)
    | MenhirState50 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv339 * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position)) * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | TOK_DIVIDE ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack)
        | TOK_MINUS ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_MODULO ->
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack)
        | TOK_PLUS ->
            _menhir_run23 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_STAR ->
            _menhir_run20 _menhir_env (Obj.magic _menhir_stack)
        | TOK_AND_AND | TOK_BAR_BAR | TOK_RPAREN ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv335 * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position)) * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position) = Obj.magic _menhir_stack in
            ((let ((_menhir_stack, _endpos_x0_, _menhir_s, (x0 : 'tv_int_expr), _startpos_x0_), _endpos_x1_, _, (x1 : 'tv_int_expr), _startpos_x1_) = _menhir_stack in
            let _10 = () in
            let _startpos = _startpos_x0_ in
            let _endpos = _endpos_x1_ in
            let _v : 'tv_bool_expr = let e2 =
              let _endpos_x_ = _endpos_x1_ in
              let _startpos_x_ = _startpos_x1_ in
              let x = x1 in
              let _endpos = _endpos_x_ in
              let _startpos = _startpos_x_ in
              
# 217 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 1470 "frontend/parser.ml"
              
            in
            let o =
              let _1 = _10 in
              
# 107 "frontend/parser.mly"
                     ( AST_GREATER )
# 1478 "frontend/parser.ml"
              
            in
            let e1 =
              let _endpos_x_ = _endpos_x0_ in
              let _startpos_x_ = _startpos_x0_ in
              let x = x0 in
              let _endpos = _endpos_x_ in
              let _startpos = _startpos_x_ in
              
# 217 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 1490 "frontend/parser.ml"
              
            in
            
# 137 "frontend/parser.mly"
    ( AST_compare (o,e1,e2) )
# 1496 "frontend/parser.ml"
             in
            _menhir_goto_bool_expr _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv336)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv337 * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position)) * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv338)) : 'freshtv340)
    | MenhirState52 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv345 * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position)) * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | TOK_DIVIDE ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack)
        | TOK_MINUS ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_MODULO ->
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack)
        | TOK_PLUS ->
            _menhir_run23 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_STAR ->
            _menhir_run20 _menhir_env (Obj.magic _menhir_stack)
        | TOK_AND_AND | TOK_BAR_BAR | TOK_RPAREN ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv341 * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position)) * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position) = Obj.magic _menhir_stack in
            ((let ((_menhir_stack, _endpos_x0_, _menhir_s, (x0 : 'tv_int_expr), _startpos_x0_), _endpos_x1_, _, (x1 : 'tv_int_expr), _startpos_x1_) = _menhir_stack in
            let _10 = () in
            let _startpos = _startpos_x0_ in
            let _endpos = _endpos_x1_ in
            let _v : 'tv_bool_expr = let e2 =
              let _endpos_x_ = _endpos_x1_ in
              let _startpos_x_ = _startpos_x1_ in
              let x = x1 in
              let _endpos = _endpos_x_ in
              let _startpos = _startpos_x_ in
              
# 217 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 1538 "frontend/parser.ml"
              
            in
            let o =
              let _1 = _10 in
              
# 110 "frontend/parser.mly"
                     ( AST_EQUAL )
# 1546 "frontend/parser.ml"
              
            in
            let e1 =
              let _endpos_x_ = _endpos_x0_ in
              let _startpos_x_ = _startpos_x0_ in
              let x = x0 in
              let _endpos = _endpos_x_ in
              let _startpos = _startpos_x_ in
              
# 217 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 1558 "frontend/parser.ml"
              
            in
            
# 137 "frontend/parser.mly"
    ( AST_compare (o,e1,e2) )
# 1564 "frontend/parser.ml"
             in
            _menhir_goto_bool_expr _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv342)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv343 * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position)) * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv344)) : 'freshtv346)
    | MenhirState38 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv349 * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | TOK_DIVIDE ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack)
        | TOK_EQUAL_EQUAL ->
            _menhir_run52 _menhir_env (Obj.magic _menhir_stack)
        | TOK_GREATER ->
            _menhir_run50 _menhir_env (Obj.magic _menhir_stack)
        | TOK_GREATER_EQUAL ->
            _menhir_run48 _menhir_env (Obj.magic _menhir_stack)
        | TOK_LESS ->
            _menhir_run46 _menhir_env (Obj.magic _menhir_stack)
        | TOK_LESS_EQUAL ->
            _menhir_run44 _menhir_env (Obj.magic _menhir_stack)
        | TOK_MINUS ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_MODULO ->
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack)
        | TOK_NOT_EQUAL ->
            _menhir_run42 _menhir_env (Obj.magic _menhir_stack)
        | TOK_PLUS ->
            _menhir_run23 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_RPAREN ->
            _menhir_run22 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p
        | TOK_STAR ->
            _menhir_run20 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv347 * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv348)) : 'freshtv350)
    | _ ->
        _menhir_fail ()

and _menhir_run7 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> (
# 56 "frontend/parser.mly"
       (string)
# 1617 "frontend/parser.ml"
) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    let _menhir_env = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv257) = Obj.magic _menhir_stack in
    let (_endpos_i_ : Lexing.position) = _endpos in
    let (_menhir_s : _menhir_state) = _menhir_s in
    let ((i : (
# 56 "frontend/parser.mly"
       (string)
# 1628 "frontend/parser.ml"
    )) : (
# 56 "frontend/parser.mly"
       (string)
# 1632 "frontend/parser.ml"
    )) = _v in
    let (_startpos_i_ : Lexing.position) = _startpos in
    ((let _startpos = _startpos_i_ in
    let _endpos = _endpos_i_ in
    let _v : 'tv_sign_int_literal = 
# 164 "frontend/parser.mly"
                       ( i )
# 1640 "frontend/parser.ml"
     in
    _menhir_goto_sign_int_literal _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv258)

and _menhir_run8 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | TOK_int _v ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv253 * _menhir_state * Lexing.position) = Obj.magic _menhir_stack in
        let (_endpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
        let (_v : (
# 56 "frontend/parser.mly"
       (string)
# 1657 "frontend/parser.ml"
        )) = _v in
        let (_startpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
        ((let _menhir_env = _menhir_discard _menhir_env in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv251 * _menhir_state * Lexing.position) = Obj.magic _menhir_stack in
        let (_endpos_i_ : Lexing.position) = _endpos in
        let ((i : (
# 56 "frontend/parser.mly"
       (string)
# 1667 "frontend/parser.ml"
        )) : (
# 56 "frontend/parser.mly"
       (string)
# 1671 "frontend/parser.ml"
        )) = _v in
        let (_startpos_i_ : Lexing.position) = _startpos in
        ((let (_menhir_stack, _menhir_s, _startpos__1_) = _menhir_stack in
        let _1 = () in
        let _startpos = _startpos__1_ in
        let _endpos = _endpos_i_ in
        let _v : 'tv_sign_int_literal = 
# 165 "frontend/parser.mly"
                       ( i )
# 1681 "frontend/parser.ml"
         in
        _menhir_goto_sign_int_literal _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv252)) : 'freshtv254)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv255 * _menhir_state * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv256)

and _menhir_run10 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | TOK_int _v ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv247 * _menhir_state * Lexing.position) = Obj.magic _menhir_stack in
        let (_endpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
        let (_v : (
# 56 "frontend/parser.mly"
       (string)
# 1705 "frontend/parser.ml"
        )) = _v in
        let (_startpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
        ((let _menhir_env = _menhir_discard _menhir_env in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv245 * _menhir_state * Lexing.position) = Obj.magic _menhir_stack in
        let (_endpos_i_ : Lexing.position) = _endpos in
        let ((i : (
# 56 "frontend/parser.mly"
       (string)
# 1715 "frontend/parser.ml"
        )) : (
# 56 "frontend/parser.mly"
       (string)
# 1719 "frontend/parser.ml"
        )) = _v in
        let (_startpos_i_ : Lexing.position) = _startpos in
        ((let (_menhir_stack, _menhir_s, _startpos__1_) = _menhir_stack in
        let _1 = () in
        let _startpos = _startpos__1_ in
        let _endpos = _endpos_i_ in
        let _v : 'tv_sign_int_literal = 
# 166 "frontend/parser.mly"
                       ( "-"^i )
# 1729 "frontend/parser.ml"
         in
        _menhir_goto_sign_int_literal _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv246)) : 'freshtv248)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv249 * _menhir_state * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv250)

and _menhir_goto_bool_expr : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> 'tv_bool_expr -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    let _menhir_stack = (_menhir_stack, _endpos, _menhir_s, _v, _startpos) in
    match _menhir_s with
    | MenhirState40 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv201 * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_bool_expr * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv199 * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_bool_expr * Lexing.position) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, _startpos__10_), _endpos_x0_, _, (x0 : 'tv_bool_expr), _startpos_x0_) = _menhir_stack in
        let _10 = () in
        let _startpos = _startpos__10_ in
        let _endpos = _endpos_x0_ in
        let _v : 'tv_bool_expr = let e =
          let _endpos_x_ = _endpos_x0_ in
          let _startpos_x_ = _startpos_x0_ in
          let x = x0 in
          let _endpos = _endpos_x_ in
          let _startpos = _startpos_x_ in
          
# 217 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 1762 "frontend/parser.ml"
          
        in
        let o =
          let _1 = _10 in
          
# 94 "frontend/parser.mly"
                     ( AST_NOT )
# 1770 "frontend/parser.ml"
          
        in
        
# 131 "frontend/parser.mly"
    ( AST_bool_unary (o,e) )
# 1776 "frontend/parser.ml"
         in
        _menhir_goto_bool_expr _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv200)) : 'freshtv202)
    | MenhirState38 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv209 * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_bool_expr * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | TOK_AND_AND ->
            _menhir_run60 _menhir_env (Obj.magic _menhir_stack)
        | TOK_BAR_BAR ->
            _menhir_run58 _menhir_env (Obj.magic _menhir_stack)
        | TOK_RPAREN ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv205 * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_bool_expr * Lexing.position) = Obj.magic _menhir_stack in
            let (_endpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv203 * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_bool_expr * Lexing.position) = Obj.magic _menhir_stack in
            let (_endpos__3_ : Lexing.position) = _endpos in
            ((let ((_menhir_stack, _menhir_s, _startpos__1_), _endpos_e_, _, (e : 'tv_bool_expr), _startpos_e_) = _menhir_stack in
            let _3 = () in
            let _1 = () in
            let _startpos = _startpos__1_ in
            let _endpos = _endpos__3_ in
            let _v : 'tv_bool_expr = 
# 122 "frontend/parser.mly"
    ( e )
# 1805 "frontend/parser.ml"
             in
            _menhir_goto_bool_expr _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv204)) : 'freshtv206)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv207 * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_bool_expr * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv208)) : 'freshtv210)
    | MenhirState58 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv215 * Lexing.position * _menhir_state * 'tv_bool_expr * Lexing.position)) * Lexing.position * _menhir_state * 'tv_bool_expr * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | TOK_AND_AND ->
            _menhir_run60 _menhir_env (Obj.magic _menhir_stack)
        | TOK_BAR_BAR | TOK_RPAREN ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv211 * Lexing.position * _menhir_state * 'tv_bool_expr * Lexing.position)) * Lexing.position * _menhir_state * 'tv_bool_expr * Lexing.position) = Obj.magic _menhir_stack in
            ((let ((_menhir_stack, _endpos_x0_, _menhir_s, (x0 : 'tv_bool_expr), _startpos_x0_), _endpos_x1_, _, (x1 : 'tv_bool_expr), _startpos_x1_) = _menhir_stack in
            let _10 = () in
            let _startpos = _startpos_x0_ in
            let _endpos = _endpos_x1_ in
            let _v : 'tv_bool_expr = let e2 =
              let _endpos_x_ = _endpos_x1_ in
              let _startpos_x_ = _startpos_x1_ in
              let x = x1 in
              let _endpos = _endpos_x_ in
              let _startpos = _startpos_x_ in
              
# 217 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 1839 "frontend/parser.ml"
              
            in
            let o =
              let _1 = _10 in
              
# 116 "frontend/parser.mly"
                     ( AST_OR )
# 1847 "frontend/parser.ml"
              
            in
            let e1 =
              let _endpos_x_ = _endpos_x0_ in
              let _startpos_x_ = _startpos_x0_ in
              let x = x0 in
              let _endpos = _endpos_x_ in
              let _startpos = _startpos_x_ in
              
# 217 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 1859 "frontend/parser.ml"
              
            in
            
# 134 "frontend/parser.mly"
    ( AST_bool_binary (o,e1,e2) )
# 1865 "frontend/parser.ml"
             in
            _menhir_goto_bool_expr _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv212)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv213 * Lexing.position * _menhir_state * 'tv_bool_expr * Lexing.position)) * Lexing.position * _menhir_state * 'tv_bool_expr * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv214)) : 'freshtv216)
    | MenhirState60 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv219 * Lexing.position * _menhir_state * 'tv_bool_expr * Lexing.position)) * Lexing.position * _menhir_state * 'tv_bool_expr * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv217 * Lexing.position * _menhir_state * 'tv_bool_expr * Lexing.position)) * Lexing.position * _menhir_state * 'tv_bool_expr * Lexing.position) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _endpos_x0_, _menhir_s, (x0 : 'tv_bool_expr), _startpos_x0_), _endpos_x1_, _, (x1 : 'tv_bool_expr), _startpos_x1_) = _menhir_stack in
        let _10 = () in
        let _startpos = _startpos_x0_ in
        let _endpos = _endpos_x1_ in
        let _v : 'tv_bool_expr = let e2 =
          let _endpos_x_ = _endpos_x1_ in
          let _startpos_x_ = _startpos_x1_ in
          let x = x1 in
          let _endpos = _endpos_x_ in
          let _startpos = _startpos_x_ in
          
# 217 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 1893 "frontend/parser.ml"
          
        in
        let o =
          let _1 = _10 in
          
# 115 "frontend/parser.mly"
                     ( AST_AND )
# 1901 "frontend/parser.ml"
          
        in
        let e1 =
          let _endpos_x_ = _endpos_x0_ in
          let _startpos_x_ = _startpos_x0_ in
          let x = x0 in
          let _endpos = _endpos_x_ in
          let _startpos = _startpos_x_ in
          
# 217 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 1913 "frontend/parser.ml"
          
        in
        
# 134 "frontend/parser.mly"
    ( AST_bool_binary (o,e1,e2) )
# 1919 "frontend/parser.ml"
         in
        _menhir_goto_bool_expr _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv218)) : 'freshtv220)
    | MenhirState36 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv225 * _menhir_state * Lexing.position) * Lexing.position) * Lexing.position * _menhir_state * 'tv_bool_expr * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | TOK_AND_AND ->
            _menhir_run60 _menhir_env (Obj.magic _menhir_stack)
        | TOK_BAR_BAR ->
            _menhir_run58 _menhir_env (Obj.magic _menhir_stack)
        | TOK_RPAREN ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv221 * _menhir_state * Lexing.position) * Lexing.position) * Lexing.position * _menhir_state * 'tv_bool_expr * Lexing.position) = Obj.magic _menhir_stack in
            let (_endpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            ((let _menhir_stack = (_menhir_stack, _endpos) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | TOK_ASSERT ->
                _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState63 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TOK_HALT ->
                _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState63 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TOK_IF ->
                _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState63 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TOK_LCURLY ->
                _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState63 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TOK_PRINT ->
                _menhir_run64 _menhir_env (Obj.magic _menhir_stack) MenhirState63 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TOK_WHILE ->
                _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState63 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TOK_id _v ->
                _menhir_run1 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState63 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState63) : 'freshtv222)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv223 * _menhir_state * Lexing.position) * Lexing.position) * Lexing.position * _menhir_state * 'tv_bool_expr * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv224)) : 'freshtv226)
    | MenhirState80 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv231 * _menhir_state * Lexing.position) * Lexing.position) * Lexing.position * _menhir_state * 'tv_bool_expr * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | TOK_AND_AND ->
            _menhir_run60 _menhir_env (Obj.magic _menhir_stack)
        | TOK_BAR_BAR ->
            _menhir_run58 _menhir_env (Obj.magic _menhir_stack)
        | TOK_RPAREN ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv227 * _menhir_state * Lexing.position) * Lexing.position) * Lexing.position * _menhir_state * 'tv_bool_expr * Lexing.position) = Obj.magic _menhir_stack in
            let (_endpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            ((let _menhir_stack = (_menhir_stack, _endpos) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | TOK_ASSERT ->
                _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState82 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TOK_HALT ->
                _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState82 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TOK_IF ->
                _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState82 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TOK_LCURLY ->
                _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState82 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TOK_PRINT ->
                _menhir_run64 _menhir_env (Obj.magic _menhir_stack) MenhirState82 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TOK_WHILE ->
                _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState82 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TOK_id _v ->
                _menhir_run1 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState82 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState82) : 'freshtv228)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv229 * _menhir_state * Lexing.position) * Lexing.position) * Lexing.position * _menhir_state * 'tv_bool_expr * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv230)) : 'freshtv232)
    | MenhirState86 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv243 * _menhir_state * Lexing.position) * Lexing.position) * Lexing.position * _menhir_state * 'tv_bool_expr * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | TOK_AND_AND ->
            _menhir_run60 _menhir_env (Obj.magic _menhir_stack)
        | TOK_BAR_BAR ->
            _menhir_run58 _menhir_env (Obj.magic _menhir_stack)
        | TOK_RPAREN ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv239 * _menhir_state * Lexing.position) * Lexing.position) * Lexing.position * _menhir_state * 'tv_bool_expr * Lexing.position) = Obj.magic _menhir_stack in
            let (_endpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            ((let _menhir_stack = (_menhir_stack, _endpos) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | TOK_SEMICOLON ->
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : ((('freshtv235 * _menhir_state * Lexing.position) * Lexing.position) * Lexing.position * _menhir_state * 'tv_bool_expr * Lexing.position) * Lexing.position) = Obj.magic _menhir_stack in
                let (_endpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
                ((let _menhir_env = _menhir_discard _menhir_env in
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : ((('freshtv233 * _menhir_state * Lexing.position) * Lexing.position) * Lexing.position * _menhir_state * 'tv_bool_expr * Lexing.position) * Lexing.position) = Obj.magic _menhir_stack in
                let (_endpos__5_ : Lexing.position) = _endpos in
                ((let ((((_menhir_stack, _menhir_s, _startpos__1_), _startpos__2_), _endpos_x0_, _, (x0 : 'tv_bool_expr), _startpos_x0_), _endpos__4_) = _menhir_stack in
                let _5 = () in
                let _4 = () in
                let _2 = () in
                let _1 = () in
                let _startpos = _startpos__1_ in
                let _endpos = _endpos__5_ in
                let _v : 'tv_stat = let e =
                  let _endpos_x_ = _endpos_x0_ in
                  let _startpos_x_ = _startpos_x0_ in
                  let x = x0 in
                  let _endpos = _endpos_x_ in
                  let _startpos = _startpos_x_ in
                  
# 217 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 2050 "frontend/parser.ml"
                  
                in
                
# 203 "frontend/parser.mly"
  ( AST_assert e )
# 2056 "frontend/parser.ml"
                 in
                _menhir_goto_stat _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv234)) : 'freshtv236)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : ((('freshtv237 * _menhir_state * Lexing.position) * Lexing.position) * Lexing.position * _menhir_state * 'tv_bool_expr * Lexing.position) * Lexing.position) = Obj.magic _menhir_stack in
                ((let ((_menhir_stack, _, _menhir_s, _, _), _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv238)) : 'freshtv240)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv241 * _menhir_state * Lexing.position) * Lexing.position) * Lexing.position * _menhir_state * 'tv_bool_expr * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv242)) : 'freshtv244)
    | _ ->
        _menhir_fail ()

and _menhir_goto_list_ext_stat__ : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_list_ext_stat__ -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState94 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv169 * Lexing.position * _menhir_state * 'tv_stat * Lexing.position) * _menhir_state * 'tv_list_ext_stat__) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv167 * Lexing.position * _menhir_state * 'tv_stat * Lexing.position) * _menhir_state * 'tv_list_ext_stat__) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _endpos_x0_, _menhir_s, (x0 : 'tv_stat), _startpos_x0_), _, (xs : 'tv_list_ext_stat__)) = _menhir_stack in
        let _v : 'tv_list_ext_stat__ = let x =
          let _endpos_x_ = _endpos_x0_ in
          let _startpos_x_ = _startpos_x0_ in
          let x = x0 in
          let _endpos = _endpos_x_ in
          let _startpos = _startpos_x_ in
          
# 217 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 2095 "frontend/parser.ml"
          
        in
        
# 188 "/home/tas/.opam/system/lib/menhir/standard.mly"
    ( x :: xs )
# 2101 "frontend/parser.ml"
         in
        _menhir_goto_list_ext_stat__ _menhir_env _menhir_stack _menhir_s _v) : 'freshtv168)) : 'freshtv170)
    | MenhirState78 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv183 * _menhir_state * Lexing.position) * _menhir_state * 'tv_list_ext_decl__) * _menhir_state * 'tv_list_ext_stat__) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | TOK_RCURLY ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv179 * _menhir_state * Lexing.position) * _menhir_state * 'tv_list_ext_decl__) * _menhir_state * 'tv_list_ext_stat__) = Obj.magic _menhir_stack in
            let (_endpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv177 * _menhir_state * Lexing.position) * _menhir_state * 'tv_list_ext_decl__) * _menhir_state * 'tv_list_ext_stat__) = Obj.magic _menhir_stack in
            let (_endpos__4_ : Lexing.position) = _endpos in
            ((let (((_menhir_stack, _menhir_s, _startpos__1_), _, (d : 'tv_list_ext_decl__)), _, (l : 'tv_list_ext_stat__)) = _menhir_stack in
            let _4 = () in
            let _1 = () in
            let _startpos = _startpos__1_ in
            let _endpos = _endpos__4_ in
            let _v : 'tv_block = 
# 175 "frontend/parser.mly"
                                                             ( d, l )
# 2126 "frontend/parser.ml"
             in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv175) = _menhir_stack in
            let (_endpos : Lexing.position) = _endpos in
            let (_menhir_s : _menhir_state) = _menhir_s in
            let (_v : 'tv_block) = _v in
            let (_startpos : Lexing.position) = _startpos in
            ((let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv173) = Obj.magic _menhir_stack in
            let (_endpos : Lexing.position) = _endpos in
            let (_menhir_s : _menhir_state) = _menhir_s in
            let (_v : 'tv_block) = _v in
            let (_startpos : Lexing.position) = _startpos in
            ((let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv171) = Obj.magic _menhir_stack in
            let (_endpos_l_ : Lexing.position) = _endpos in
            let (_menhir_s : _menhir_state) = _menhir_s in
            let ((l : 'tv_block) : 'tv_block) = _v in
            let (_startpos_l_ : Lexing.position) = _startpos in
            ((let _startpos = _startpos_l_ in
            let _endpos = _endpos_l_ in
            let _v : 'tv_stat = 
# 188 "frontend/parser.mly"
  ( AST_block (fst l, snd l) )
# 2151 "frontend/parser.ml"
             in
            _menhir_goto_stat _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv172)) : 'freshtv174)) : 'freshtv176)) : 'freshtv178)) : 'freshtv180)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv181 * _menhir_state * Lexing.position) * _menhir_state * 'tv_list_ext_decl__) * _menhir_state * 'tv_list_ext_stat__) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv182)) : 'freshtv184)
    | MenhirState0 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv197 * _menhir_state * 'tv_list_ext_stat__) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | TOK_EOF ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv193 * _menhir_state * 'tv_list_ext_stat__) = Obj.magic _menhir_stack in
            ((let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv191 * _menhir_state * 'tv_list_ext_stat__) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, (t : 'tv_list_ext_stat__)) = _menhir_stack in
            let _2 = () in
            let _v : (
# 71 "frontend/parser.mly"
      (Abstract_syntax_tree.prog)
# 2177 "frontend/parser.ml"
            ) = 
# 80 "frontend/parser.mly"
                                ( t )
# 2181 "frontend/parser.ml"
             in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv189) = _menhir_stack in
            let (_menhir_s : _menhir_state) = _menhir_s in
            let (_v : (
# 71 "frontend/parser.mly"
      (Abstract_syntax_tree.prog)
# 2189 "frontend/parser.ml"
            )) = _v in
            ((let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv187) = Obj.magic _menhir_stack in
            let (_menhir_s : _menhir_state) = _menhir_s in
            let (_v : (
# 71 "frontend/parser.mly"
      (Abstract_syntax_tree.prog)
# 2197 "frontend/parser.ml"
            )) = _v in
            ((let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv185) = Obj.magic _menhir_stack in
            let (_menhir_s : _menhir_state) = _menhir_s in
            let ((_1 : (
# 71 "frontend/parser.mly"
      (Abstract_syntax_tree.prog)
# 2205 "frontend/parser.ml"
            )) : (
# 71 "frontend/parser.mly"
      (Abstract_syntax_tree.prog)
# 2209 "frontend/parser.ml"
            )) = _v in
            (Obj.magic _1 : 'freshtv186)) : 'freshtv188)) : 'freshtv190)) : 'freshtv192)) : 'freshtv194)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv195 * _menhir_state * 'tv_list_ext_stat__) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv196)) : 'freshtv198)
    | _ ->
        _menhir_fail ()

and _menhir_run18 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | TOK_LPAREN ->
        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState18 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_MINUS ->
        _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState18 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_PLUS ->
        _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState18 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_RAND ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState18 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_id _v ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState18 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_int _v ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState18 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState18

and _menhir_goto_loption_separated_nonempty_list_TOK_COMMA_ext_TOK_id___ : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_loption_separated_nonempty_list_TOK_COMMA_ext_TOK_id___ -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : (('freshtv165 * _menhir_state * Lexing.position) * Lexing.position) * _menhir_state * 'tv_loption_separated_nonempty_list_TOK_COMMA_ext_TOK_id___) = Obj.magic _menhir_stack in
    ((assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | TOK_RPAREN ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv161 * _menhir_state * Lexing.position) * Lexing.position) * _menhir_state * 'tv_loption_separated_nonempty_list_TOK_COMMA_ext_TOK_id___) = Obj.magic _menhir_stack in
        let (_endpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
        ((let _menhir_stack = (_menhir_stack, _endpos) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | TOK_SEMICOLON ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv157 * _menhir_state * Lexing.position) * Lexing.position) * _menhir_state * 'tv_loption_separated_nonempty_list_TOK_COMMA_ext_TOK_id___) * Lexing.position) = Obj.magic _menhir_stack in
            let (_endpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv155 * _menhir_state * Lexing.position) * Lexing.position) * _menhir_state * 'tv_loption_separated_nonempty_list_TOK_COMMA_ext_TOK_id___) * Lexing.position) = Obj.magic _menhir_stack in
            let (_endpos__5_ : Lexing.position) = _endpos in
            ((let ((((_menhir_stack, _menhir_s, _startpos__1_), _startpos__2_), _, (xs0 : 'tv_loption_separated_nonempty_list_TOK_COMMA_ext_TOK_id___)), _endpos__4_) = _menhir_stack in
            let _5 = () in
            let _4 = () in
            let _2 = () in
            let _1 = () in
            let _startpos = _startpos__1_ in
            let _endpos = _endpos__5_ in
            let _v : 'tv_stat = let l =
              let xs = xs0 in
              
# 207 "/home/tas/.opam/system/lib/menhir/standard.mly"
    ( xs )
# 2281 "frontend/parser.ml"
              
            in
            
# 206 "frontend/parser.mly"
  ( AST_print l )
# 2287 "frontend/parser.ml"
             in
            _menhir_goto_stat _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv156)) : 'freshtv158)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv159 * _menhir_state * Lexing.position) * Lexing.position) * _menhir_state * 'tv_loption_separated_nonempty_list_TOK_COMMA_ext_TOK_id___) * Lexing.position) = Obj.magic _menhir_stack in
            ((let ((_menhir_stack, _menhir_s, _), _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv160)) : 'freshtv162)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv163 * _menhir_state * Lexing.position) * Lexing.position) * _menhir_state * 'tv_loption_separated_nonempty_list_TOK_COMMA_ext_TOK_id___) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv164)) : 'freshtv166)

and _menhir_run66 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> (
# 55 "frontend/parser.mly"
       (string)
# 2308 "frontend/parser.ml"
) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    let _menhir_stack = (_menhir_stack, _endpos, _menhir_s, _v, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | TOK_COMMA ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv149 * Lexing.position * _menhir_state * (
# 55 "frontend/parser.mly"
       (string)
# 2320 "frontend/parser.ml"
        ) * Lexing.position) = Obj.magic _menhir_stack in
        ((let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | TOK_id _v ->
            _menhir_run66 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState67 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState67) : 'freshtv150)
    | TOK_RPAREN ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv151 * Lexing.position * _menhir_state * (
# 55 "frontend/parser.mly"
       (string)
# 2336 "frontend/parser.ml"
        ) * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _endpos_x0_, _menhir_s, (x0 : (
# 55 "frontend/parser.mly"
       (string)
# 2341 "frontend/parser.ml"
        )), _startpos_x0_) = _menhir_stack in
        let _v : 'tv_separated_nonempty_list_TOK_COMMA_ext_TOK_id__ = let x =
          let _endpos_x_ = _endpos_x0_ in
          let _startpos_x_ = _startpos_x0_ in
          let x = x0 in
          let _endpos = _endpos_x_ in
          let _startpos = _startpos_x_ in
          
# 217 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 2352 "frontend/parser.ml"
          
        in
        
# 216 "/home/tas/.opam/system/lib/menhir/standard.mly"
    ( [ x ] )
# 2358 "frontend/parser.ml"
         in
        _menhir_goto_separated_nonempty_list_TOK_COMMA_ext_TOK_id__ _menhir_env _menhir_stack _menhir_s _v) : 'freshtv152)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv153 * Lexing.position * _menhir_state * (
# 55 "frontend/parser.mly"
       (string)
# 2368 "frontend/parser.ml"
        ) * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv154)

and _menhir_reduce27 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _v : 'tv_list_ext_decl__ = 
# 186 "/home/tas/.opam/system/lib/menhir/standard.mly"
    ( [] )
# 2378 "frontend/parser.ml"
     in
    _menhir_goto_list_ext_decl__ _menhir_env _menhir_stack _menhir_s _v

and _menhir_run74 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_env = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv147) = Obj.magic _menhir_stack in
    let (_menhir_s : _menhir_state) = _menhir_s in
    let (_startpos__1_ : Lexing.position) = _startpos in
    ((let _1 = () in
    let _startpos = _startpos__1_ in
    let _v : 'tv_typ = 
# 183 "frontend/parser.mly"
          ( AST_INT )
# 2394 "frontend/parser.ml"
     in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv145) = _menhir_stack in
    let (_menhir_s : _menhir_state) = _menhir_s in
    let (_v : 'tv_typ) = _v in
    let (_startpos : Lexing.position) = _startpos in
    ((let _menhir_stack = (_menhir_stack, _menhir_s, _v, _startpos) in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv143 * _menhir_state * 'tv_typ * Lexing.position) = Obj.magic _menhir_stack in
    ((assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | TOK_id _v ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv139 * _menhir_state * 'tv_typ * Lexing.position) = Obj.magic _menhir_stack in
        let (_endpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
        let (_v : (
# 55 "frontend/parser.mly"
       (string)
# 2414 "frontend/parser.ml"
        )) = _v in
        let (_startpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
        ((let _menhir_stack = (_menhir_stack, _endpos, _v, _startpos) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | TOK_SEMICOLON ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv135 * _menhir_state * 'tv_typ * Lexing.position) * Lexing.position * (
# 55 "frontend/parser.mly"
       (string)
# 2426 "frontend/parser.ml"
            ) * Lexing.position) = Obj.magic _menhir_stack in
            let (_endpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv133 * _menhir_state * 'tv_typ * Lexing.position) * Lexing.position * (
# 55 "frontend/parser.mly"
       (string)
# 2434 "frontend/parser.ml"
            ) * Lexing.position) = Obj.magic _menhir_stack in
            let (_endpos__3_ : Lexing.position) = _endpos in
            ((let ((_menhir_stack, _menhir_s, (t : 'tv_typ), _startpos_t_), _endpos_v_, (v : (
# 55 "frontend/parser.mly"
       (string)
# 2440 "frontend/parser.ml"
            )), _startpos_v_) = _menhir_stack in
            let _3 = () in
            let _startpos = _startpos_t_ in
            let _endpos = _endpos__3_ in
            let _v : 'tv_decl = 
# 179 "frontend/parser.mly"
                               ( t, v )
# 2448 "frontend/parser.ml"
             in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv131) = _menhir_stack in
            let (_endpos : Lexing.position) = _endpos in
            let (_menhir_s : _menhir_state) = _menhir_s in
            let (_v : 'tv_decl) = _v in
            let (_startpos : Lexing.position) = _startpos in
            ((let _menhir_stack = (_menhir_stack, _endpos, _menhir_s, _v, _startpos) in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv129 * Lexing.position * _menhir_state * 'tv_decl * Lexing.position) = Obj.magic _menhir_stack in
            ((assert (not _menhir_env._menhir_error);
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | TOK_INT ->
                _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState98 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TOK_ASSERT | TOK_HALT | TOK_IF | TOK_LCURLY | TOK_PRINT | TOK_RCURLY | TOK_WHILE | TOK_id _ ->
                _menhir_reduce27 _menhir_env (Obj.magic _menhir_stack) MenhirState98
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState98) : 'freshtv130)) : 'freshtv132)) : 'freshtv134)) : 'freshtv136)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv137 * _menhir_state * 'tv_typ * Lexing.position) * Lexing.position * (
# 55 "frontend/parser.mly"
       (string)
# 2477 "frontend/parser.ml"
            ) * Lexing.position) = Obj.magic _menhir_stack in
            ((let ((_menhir_stack, _menhir_s, _, _), _, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv138)) : 'freshtv140)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv141 * _menhir_state * 'tv_typ * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv142)) : 'freshtv144)) : 'freshtv146)) : 'freshtv148)

and _menhir_goto_stat : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> 'tv_stat -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    let _menhir_stack = (_menhir_stack, _endpos, _menhir_s, _v, _startpos) in
    match _menhir_s with
    | MenhirState82 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (((('freshtv117 * _menhir_state * Lexing.position) * Lexing.position) * Lexing.position * _menhir_state * 'tv_bool_expr * Lexing.position) * Lexing.position) * Lexing.position * _menhir_state * 'tv_stat * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | TOK_ELSE ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (((('freshtv111 * _menhir_state * Lexing.position) * Lexing.position) * Lexing.position * _menhir_state * 'tv_bool_expr * Lexing.position) * Lexing.position) * Lexing.position * _menhir_state * 'tv_stat * Lexing.position) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | TOK_ASSERT ->
                _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState91 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TOK_HALT ->
                _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState91 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TOK_IF ->
                _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState91 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TOK_LCURLY ->
                _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState91 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TOK_PRINT ->
                _menhir_run64 _menhir_env (Obj.magic _menhir_stack) MenhirState91 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TOK_WHILE ->
                _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState91 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TOK_id _v ->
                _menhir_run1 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState91 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState91) : 'freshtv112)
        | TOK_ASSERT | TOK_EOF | TOK_HALT | TOK_IF | TOK_LCURLY | TOK_PRINT | TOK_RCURLY | TOK_WHILE | TOK_id _ ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (((('freshtv113 * _menhir_state * Lexing.position) * Lexing.position) * Lexing.position * _menhir_state * 'tv_bool_expr * Lexing.position) * Lexing.position) * Lexing.position * _menhir_state * 'tv_stat * Lexing.position) = Obj.magic _menhir_stack in
            ((let (((((_menhir_stack, _menhir_s, _startpos__1_), _startpos__2_), _endpos_x0_, _, (x0 : 'tv_bool_expr), _startpos_x0_), _endpos__4_), _endpos_x1_, _, (x1 : 'tv_stat), _startpos_x1_) = _menhir_stack in
            let _4 = () in
            let _2 = () in
            let _1 = () in
            let _startpos = _startpos__1_ in
            let _endpos = _endpos_x1_ in
            let _v : 'tv_stat = let s =
              let _endpos_x_ = _endpos_x1_ in
              let _startpos_x_ = _startpos_x1_ in
              let x = x1 in
              let _endpos = _endpos_x_ in
              let _startpos = _startpos_x_ in
              
# 217 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 2541 "frontend/parser.ml"
              
            in
            let e =
              let _endpos_x_ = _endpos_x0_ in
              let _startpos_x_ = _startpos_x0_ in
              let x = x0 in
              let _endpos = _endpos_x_ in
              let _startpos = _startpos_x_ in
              
# 217 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 2553 "frontend/parser.ml"
              
            in
            
# 194 "frontend/parser.mly"
  ( AST_if (e, s, None) )
# 2559 "frontend/parser.ml"
             in
            _menhir_goto_stat _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv114)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (((('freshtv115 * _menhir_state * Lexing.position) * Lexing.position) * Lexing.position * _menhir_state * 'tv_bool_expr * Lexing.position) * Lexing.position) * Lexing.position * _menhir_state * 'tv_stat * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv116)) : 'freshtv118)
    | MenhirState91 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (((((('freshtv121 * _menhir_state * Lexing.position) * Lexing.position) * Lexing.position * _menhir_state * 'tv_bool_expr * Lexing.position) * Lexing.position) * Lexing.position * _menhir_state * 'tv_stat * Lexing.position)) * Lexing.position * _menhir_state * 'tv_stat * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (((((('freshtv119 * _menhir_state * Lexing.position) * Lexing.position) * Lexing.position * _menhir_state * 'tv_bool_expr * Lexing.position) * Lexing.position) * Lexing.position * _menhir_state * 'tv_stat * Lexing.position)) * Lexing.position * _menhir_state * 'tv_stat * Lexing.position) = Obj.magic _menhir_stack in
        ((let ((((((_menhir_stack, _menhir_s, _startpos__1_), _startpos__2_), _endpos_x0_, _, (x0 : 'tv_bool_expr), _startpos_x0_), _endpos__4_), _endpos_x1_, _, (x1 : 'tv_stat), _startpos_x1_), _endpos_x2_, _, (x2 : 'tv_stat), _startpos_x2_) = _menhir_stack in
        let _6 = () in
        let _4 = () in
        let _2 = () in
        let _1 = () in
        let _startpos = _startpos__1_ in
        let _endpos = _endpos_x2_ in
        let _v : 'tv_stat = let t =
          let _endpos_x_ = _endpos_x2_ in
          let _startpos_x_ = _startpos_x2_ in
          let x = x2 in
          let _endpos = _endpos_x_ in
          let _startpos = _startpos_x_ in
          
# 217 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 2590 "frontend/parser.ml"
          
        in
        let s =
          let _endpos_x_ = _endpos_x1_ in
          let _startpos_x_ = _startpos_x1_ in
          let x = x1 in
          let _endpos = _endpos_x_ in
          let _startpos = _startpos_x_ in
          
# 217 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 2602 "frontend/parser.ml"
          
        in
        let e =
          let _endpos_x_ = _endpos_x0_ in
          let _startpos_x_ = _startpos_x0_ in
          let x = x0 in
          let _endpos = _endpos_x_ in
          let _startpos = _startpos_x_ in
          
# 217 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 2614 "frontend/parser.ml"
          
        in
        
# 197 "frontend/parser.mly"
  ( AST_if (e, s, Some t) )
# 2620 "frontend/parser.ml"
         in
        _menhir_goto_stat _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv120)) : 'freshtv122)
    | MenhirState0 | MenhirState94 | MenhirState78 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv123 * Lexing.position * _menhir_state * 'tv_stat * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | TOK_ASSERT ->
            _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState94 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_HALT ->
            _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState94 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_IF ->
            _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState94 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_LCURLY ->
            _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState94 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_PRINT ->
            _menhir_run64 _menhir_env (Obj.magic _menhir_stack) MenhirState94 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_WHILE ->
            _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState94 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_id _v ->
            _menhir_run1 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState94 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_EOF | TOK_RCURLY ->
            _menhir_reduce29 _menhir_env (Obj.magic _menhir_stack) MenhirState94
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState94) : 'freshtv124)
    | MenhirState63 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (((('freshtv127 * _menhir_state * Lexing.position) * Lexing.position) * Lexing.position * _menhir_state * 'tv_bool_expr * Lexing.position) * Lexing.position) * Lexing.position * _menhir_state * 'tv_stat * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (((('freshtv125 * _menhir_state * Lexing.position) * Lexing.position) * Lexing.position * _menhir_state * 'tv_bool_expr * Lexing.position) * Lexing.position) * Lexing.position * _menhir_state * 'tv_stat * Lexing.position) = Obj.magic _menhir_stack in
        ((let (((((_menhir_stack, _menhir_s, _startpos__1_), _startpos__2_), _endpos_x0_, _, (x0 : 'tv_bool_expr), _startpos_x0_), _endpos__4_), _endpos_x1_, _, (x1 : 'tv_stat), _startpos_x1_) = _menhir_stack in
        let _4 = () in
        let _2 = () in
        let _1 = () in
        let _startpos = _startpos__1_ in
        let _endpos = _endpos_x1_ in
        let _v : 'tv_stat = let s =
          let _endpos_x_ = _endpos_x1_ in
          let _startpos_x_ = _startpos_x1_ in
          let x = x1 in
          let _endpos = _endpos_x_ in
          let _startpos = _startpos_x_ in
          
# 217 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 2669 "frontend/parser.ml"
          
        in
        let e =
          let _endpos_x_ = _endpos_x0_ in
          let _startpos_x_ = _startpos_x0_ in
          let x = x0 in
          let _endpos = _endpos_x_ in
          let _startpos = _startpos_x_ in
          
# 217 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 2681 "frontend/parser.ml"
          
        in
        
# 200 "frontend/parser.mly"
  ( AST_while (e, s) )
# 2687 "frontend/parser.ml"
         in
        _menhir_goto_stat _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv126)) : 'freshtv128)
    | _ ->
        _menhir_fail ()

and _menhir_run3 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> (
# 56 "frontend/parser.mly"
       (string)
# 2696 "frontend/parser.ml"
) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    let _menhir_env = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv109) = Obj.magic _menhir_stack in
    let (_endpos_x0_ : Lexing.position) = _endpos in
    let (_menhir_s : _menhir_state) = _menhir_s in
    let ((x0 : (
# 56 "frontend/parser.mly"
       (string)
# 2707 "frontend/parser.ml"
    )) : (
# 56 "frontend/parser.mly"
       (string)
# 2711 "frontend/parser.ml"
    )) = _v in
    let (_startpos_x0_ : Lexing.position) = _startpos in
    ((let _startpos = _startpos_x0_ in
    let _endpos = _endpos_x0_ in
    let _v : 'tv_int_expr = let e =
      let _endpos_x_ = _endpos_x0_ in
      let _startpos_x_ = _startpos_x0_ in
      let x = x0 in
      let _endpos = _endpos_x_ in
      let _startpos = _startpos_x_ in
      
# 217 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 2725 "frontend/parser.ml"
      
    in
    
# 146 "frontend/parser.mly"
    ( AST_int_const e )
# 2731 "frontend/parser.ml"
     in
    _menhir_goto_int_expr _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv110)

and _menhir_run4 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> (
# 55 "frontend/parser.mly"
       (string)
# 2738 "frontend/parser.ml"
) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    let _menhir_env = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv107) = Obj.magic _menhir_stack in
    let (_endpos_x0_ : Lexing.position) = _endpos in
    let (_menhir_s : _menhir_state) = _menhir_s in
    let ((x0 : (
# 55 "frontend/parser.mly"
       (string)
# 2749 "frontend/parser.ml"
    )) : (
# 55 "frontend/parser.mly"
       (string)
# 2753 "frontend/parser.ml"
    )) = _v in
    let (_startpos_x0_ : Lexing.position) = _startpos in
    ((let _startpos = _startpos_x0_ in
    let _endpos = _endpos_x0_ in
    let _v : 'tv_int_expr = let e =
      let _endpos_x_ = _endpos_x0_ in
      let _startpos_x_ = _startpos_x0_ in
      let x = x0 in
      let _endpos = _endpos_x_ in
      let _startpos = _startpos_x_ in
      
# 217 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 2767 "frontend/parser.ml"
      
    in
    
# 149 "frontend/parser.mly"
    ( AST_identifier e )
# 2773 "frontend/parser.ml"
     in
    _menhir_goto_int_expr _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv108)

and _menhir_run37 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _startpos ->
    let _menhir_env = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv105) = Obj.magic _menhir_stack in
    let (_endpos__1_ : Lexing.position) = _endpos in
    let (_menhir_s : _menhir_state) = _menhir_s in
    let (_startpos__1_ : Lexing.position) = _startpos in
    ((let _1 = () in
    let _startpos = _startpos__1_ in
    let _endpos = _endpos__1_ in
    let _v : 'tv_bool_expr = 
# 125 "frontend/parser.mly"
    ( AST_bool_const true )
# 2791 "frontend/parser.ml"
     in
    _menhir_goto_bool_expr _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv106)

and _menhir_run5 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | TOK_LPAREN ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv101 * _menhir_state * Lexing.position) = Obj.magic _menhir_stack in
        let (_startpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
        ((let _menhir_stack = (_menhir_stack, _startpos) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | TOK_MINUS ->
            _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState6 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_PLUS ->
            _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState6 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_int _v ->
            _menhir_run7 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState6 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState6) : 'freshtv102)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv103 * _menhir_state * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv104)

and _menhir_run16 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | TOK_LPAREN ->
        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState16 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_MINUS ->
        _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState16 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_PLUS ->
        _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState16 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_RAND ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState16 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_id _v ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState16 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_int _v ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState16 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState16

and _menhir_run17 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | TOK_LPAREN ->
        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState17 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_MINUS ->
        _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState17 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_PLUS ->
        _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState17 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_RAND ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState17 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_id _v ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState17 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_int _v ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState17 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState17

and _menhir_run38 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | TOK_EXCLAIM ->
        _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState38 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_FALSE ->
        _menhir_run39 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState38 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_LPAREN ->
        _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState38 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_MINUS ->
        _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState38 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_PLUS ->
        _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState38 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_RAND ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState38 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_TRUE ->
        _menhir_run37 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState38 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_id _v ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState38 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_int _v ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState38 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState38

and _menhir_run39 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _startpos ->
    let _menhir_env = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv99) = Obj.magic _menhir_stack in
    let (_endpos__1_ : Lexing.position) = _endpos in
    let (_menhir_s : _menhir_state) = _menhir_s in
    let (_startpos__1_ : Lexing.position) = _startpos in
    ((let _1 = () in
    let _startpos = _startpos__1_ in
    let _endpos = _endpos__1_ in
    let _v : 'tv_bool_expr = 
# 128 "frontend/parser.mly"
    ( AST_bool_const false )
# 2916 "frontend/parser.ml"
     in
    _menhir_goto_bool_expr _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv100)

and _menhir_run40 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | TOK_EXCLAIM ->
        _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState40 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_FALSE ->
        _menhir_run39 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState40 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_LPAREN ->
        _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState40 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_MINUS ->
        _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState40 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_PLUS ->
        _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState40 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_RAND ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState40 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_TRUE ->
        _menhir_run37 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState40 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_id _v ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState40 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_int _v ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState40 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState40

and _menhir_errorcase : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    match _menhir_s with
    | MenhirState98 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv31 * Lexing.position * _menhir_state * 'tv_decl * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv32)
    | MenhirState94 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv33 * Lexing.position * _menhir_state * 'tv_stat * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv34)
    | MenhirState91 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((((('freshtv35 * _menhir_state * Lexing.position) * Lexing.position) * Lexing.position * _menhir_state * 'tv_bool_expr * Lexing.position) * Lexing.position) * Lexing.position * _menhir_state * 'tv_stat * Lexing.position)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv36)
    | MenhirState86 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv37 * _menhir_state * Lexing.position) * Lexing.position) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv38)
    | MenhirState82 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv39 * _menhir_state * Lexing.position) * Lexing.position) * Lexing.position * _menhir_state * 'tv_bool_expr * Lexing.position) * Lexing.position) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _, _menhir_s, _, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv40)
    | MenhirState80 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv41 * _menhir_state * Lexing.position) * Lexing.position) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv42)
    | MenhirState78 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv43 * _menhir_state * Lexing.position) * _menhir_state * 'tv_list_ext_decl__) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv44)
    | MenhirState73 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv45 * _menhir_state * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv46)
    | MenhirState67 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv47 * Lexing.position * _menhir_state * (
# 55 "frontend/parser.mly"
       (string)
# 2997 "frontend/parser.ml"
        ) * Lexing.position)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv48)
    | MenhirState65 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv49 * _menhir_state * Lexing.position) * Lexing.position) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv50)
    | MenhirState63 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv51 * _menhir_state * Lexing.position) * Lexing.position) * Lexing.position * _menhir_state * 'tv_bool_expr * Lexing.position) * Lexing.position) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _, _menhir_s, _, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv52)
    | MenhirState60 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv53 * Lexing.position * _menhir_state * 'tv_bool_expr * Lexing.position)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv54)
    | MenhirState58 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv55 * Lexing.position * _menhir_state * 'tv_bool_expr * Lexing.position)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv56)
    | MenhirState52 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv57 * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv58)
    | MenhirState50 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv59 * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv60)
    | MenhirState48 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv61 * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv62)
    | MenhirState46 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv63 * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv64)
    | MenhirState44 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv65 * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv66)
    | MenhirState42 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv67 * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv68)
    | MenhirState40 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv69 * _menhir_state * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv70)
    | MenhirState38 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv71 * _menhir_state * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv72)
    | MenhirState36 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv73 * _menhir_state * Lexing.position) * Lexing.position) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv74)
    | MenhirState29 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv75 * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position) * Lexing.position) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _, _menhir_s, _, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv76)
    | MenhirState27 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv77 * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv78)
    | MenhirState25 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv79 * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv80)
    | MenhirState23 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv81 * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position) * Lexing.position) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _, _menhir_s, _, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv82)
    | MenhirState20 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv83 * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv84)
    | MenhirState18 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv85 * _menhir_state * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv86)
    | MenhirState17 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv87 * _menhir_state * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv88)
    | MenhirState16 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv89 * _menhir_state * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv90)
    | MenhirState13 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv91 * _menhir_state * Lexing.position) * Lexing.position) * Lexing.position * _menhir_state * 'tv_sign_int_literal * Lexing.position)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv92)
    | MenhirState6 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv93 * _menhir_state * Lexing.position) * Lexing.position) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv94)
    | MenhirState2 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv95 * Lexing.position * _menhir_state * (
# 55 "frontend/parser.mly"
       (string)
# 3121 "frontend/parser.ml"
        ) * Lexing.position)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv96)
    | MenhirState0 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv97) = Obj.magic _menhir_stack in
        (raise _eRR : 'freshtv98)

and _menhir_reduce29 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _v : 'tv_list_ext_stat__ = 
# 186 "/home/tas/.opam/system/lib/menhir/standard.mly"
    ( [] )
# 3135 "frontend/parser.ml"
     in
    _menhir_goto_list_ext_stat__ _menhir_env _menhir_stack _menhir_s _v

and _menhir_run1 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> (
# 55 "frontend/parser.mly"
       (string)
# 3142 "frontend/parser.ml"
) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    let _menhir_stack = (_menhir_stack, _endpos, _menhir_s, _v, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | TOK_EQUAL ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv27 * Lexing.position * _menhir_state * (
# 55 "frontend/parser.mly"
       (string)
# 3154 "frontend/parser.ml"
        ) * Lexing.position) = Obj.magic _menhir_stack in
        ((let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | TOK_LPAREN ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState2 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_MINUS ->
            _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState2 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_PLUS ->
            _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState2 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_RAND ->
            _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState2 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_id _v ->
            _menhir_run4 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState2 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_int _v ->
            _menhir_run3 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState2 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState2) : 'freshtv28)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv29 * Lexing.position * _menhir_state * (
# 55 "frontend/parser.mly"
       (string)
# 3182 "frontend/parser.ml"
        ) * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv30)

and _menhir_run35 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | TOK_LPAREN ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv23 * _menhir_state * Lexing.position) = Obj.magic _menhir_stack in
        let (_startpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
        ((let _menhir_stack = (_menhir_stack, _startpos) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | TOK_EXCLAIM ->
            _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState36 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_FALSE ->
            _menhir_run39 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState36 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_LPAREN ->
            _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState36 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_MINUS ->
            _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState36 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_PLUS ->
            _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState36 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_RAND ->
            _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState36 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_TRUE ->
            _menhir_run37 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState36 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_id _v ->
            _menhir_run4 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState36 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_int _v ->
            _menhir_run3 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState36 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState36) : 'freshtv24)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv25 * _menhir_state * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv26)

and _menhir_run64 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | TOK_LPAREN ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv19 * _menhir_state * Lexing.position) = Obj.magic _menhir_stack in
        let (_startpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
        ((let _menhir_stack = (_menhir_stack, _startpos) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | TOK_id _v ->
            _menhir_run66 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState65 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_RPAREN ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv17) = Obj.magic _menhir_stack in
            let (_menhir_s : _menhir_state) = MenhirState65 in
            ((let _v : 'tv_loption_separated_nonempty_list_TOK_COMMA_ext_TOK_id___ = 
# 129 "/home/tas/.opam/system/lib/menhir/standard.mly"
    ( [] )
# 3254 "frontend/parser.ml"
             in
            _menhir_goto_loption_separated_nonempty_list_TOK_COMMA_ext_TOK_id___ _menhir_env _menhir_stack _menhir_s _v) : 'freshtv18)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState65) : 'freshtv20)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv21 * _menhir_state * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv22)

and _menhir_run73 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | TOK_INT ->
        _menhir_run74 _menhir_env (Obj.magic _menhir_stack) MenhirState73 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_ASSERT | TOK_HALT | TOK_IF | TOK_LCURLY | TOK_PRINT | TOK_RCURLY | TOK_WHILE | TOK_id _ ->
        _menhir_reduce27 _menhir_env (Obj.magic _menhir_stack) MenhirState73
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState73

and _menhir_run79 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | TOK_LPAREN ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv13 * _menhir_state * Lexing.position) = Obj.magic _menhir_stack in
        let (_startpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
        ((let _menhir_stack = (_menhir_stack, _startpos) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | TOK_EXCLAIM ->
            _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState80 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_FALSE ->
            _menhir_run39 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState80 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_LPAREN ->
            _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState80 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_MINUS ->
            _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState80 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_PLUS ->
            _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState80 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_RAND ->
            _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState80 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_TRUE ->
            _menhir_run37 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState80 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_id _v ->
            _menhir_run4 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState80 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_int _v ->
            _menhir_run3 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState80 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState80) : 'freshtv14)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv15 * _menhir_state * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv16)

and _menhir_run83 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | TOK_SEMICOLON ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv9 * _menhir_state * Lexing.position) = Obj.magic _menhir_stack in
        let (_endpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
        ((let _menhir_env = _menhir_discard _menhir_env in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv7 * _menhir_state * Lexing.position) = Obj.magic _menhir_stack in
        let (_endpos__2_ : Lexing.position) = _endpos in
        ((let (_menhir_stack, _menhir_s, _startpos__1_) = _menhir_stack in
        let _2 = () in
        let _1 = () in
        let _startpos = _startpos__1_ in
        let _endpos = _endpos__2_ in
        let _v : 'tv_stat = 
# 209 "frontend/parser.mly"
  ( AST_HALT )
# 3350 "frontend/parser.ml"
         in
        _menhir_goto_stat _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv8)) : 'freshtv10)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv11 * _menhir_state * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv12)

and _menhir_run85 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | TOK_LPAREN ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv3 * _menhir_state * Lexing.position) = Obj.magic _menhir_stack in
        let (_startpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
        ((let _menhir_stack = (_menhir_stack, _startpos) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | TOK_EXCLAIM ->
            _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState86 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_FALSE ->
            _menhir_run39 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState86 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_LPAREN ->
            _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState86 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_MINUS ->
            _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState86 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_PLUS ->
            _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState86 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_RAND ->
            _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState86 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_TRUE ->
            _menhir_run37 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState86 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_id _v ->
            _menhir_run4 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState86 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_int _v ->
            _menhir_run3 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState86 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState86) : 'freshtv4)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv5 * _menhir_state * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv6)

and _menhir_discard : _menhir_env -> _menhir_env =
  fun _menhir_env ->
    let lexer = _menhir_env._menhir_lexer in
    let lexbuf = _menhir_env._menhir_lexbuf in
    let _tok = lexer lexbuf in
    {
      _menhir_lexer = lexer;
      _menhir_lexbuf = lexbuf;
      _menhir_token = _tok;
      _menhir_error = false;
    }

and file : (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (
# 71 "frontend/parser.mly"
      (Abstract_syntax_tree.prog)
# 3420 "frontend/parser.ml"
) =
  fun lexer lexbuf ->
    let _menhir_env =
      let (lexer : Lexing.lexbuf -> token) = lexer in
      let (lexbuf : Lexing.lexbuf) = lexbuf in
      ((let _tok = Obj.magic () in
      {
        _menhir_lexer = lexer;
        _menhir_lexbuf = lexbuf;
        _menhir_token = _tok;
        _menhir_error = false;
      }) : _menhir_env)
    in
    Obj.magic (let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv1) = ((), _menhir_env._menhir_lexbuf.Lexing.lex_curr_p) in
    ((let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | TOK_ASSERT ->
        _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState0 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_HALT ->
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState0 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_IF ->
        _menhir_run79 _menhir_env (Obj.magic _menhir_stack) MenhirState0 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_LCURLY ->
        _menhir_run73 _menhir_env (Obj.magic _menhir_stack) MenhirState0 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_PRINT ->
        _menhir_run64 _menhir_env (Obj.magic _menhir_stack) MenhirState0 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_WHILE ->
        _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState0 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_id _v ->
        _menhir_run1 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState0 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_EOF ->
        _menhir_reduce29 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState0) : 'freshtv2))

# 220 "frontend/parser.mly"
  

# 3463 "frontend/parser.ml"

# 220 "/home/tas/.opam/system/lib/menhir/standard.mly"
  


# 3469 "frontend/parser.ml"
