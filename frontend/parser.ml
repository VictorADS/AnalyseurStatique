
module Basics = struct
  
  exception Error
  
  type token = 
    | TOK_int of (
# 55 "frontend/parser.mly"
       (string)
# 11 "frontend/parser.ml"
  )
    | TOK_id of (
# 54 "frontend/parser.mly"
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
  | MenhirState96
  | MenhirState92
  | MenhirState89
  | MenhirState84
  | MenhirState80
  | MenhirState78
  | MenhirState76
  | MenhirState71
  | MenhirState65
  | MenhirState63
  | MenhirState61
  | MenhirState58
  | MenhirState56
  | MenhirState50
  | MenhirState48
  | MenhirState46
  | MenhirState44
  | MenhirState42
  | MenhirState40
  | MenhirState38
  | MenhirState36
  | MenhirState34
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

# 103 "frontend/parser.ml"

let rec _menhir_run40 : _menhir_env -> 'ttv_tail * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | TOK_LPAREN ->
        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState40 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_MINUS ->
        _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState40 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_PLUS ->
        _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState40 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_RAND ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState40 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_id _v ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState40 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_int _v ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState40 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState40

and _menhir_run42 : _menhir_env -> 'ttv_tail * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position -> 'ttv_return =
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
    let (_menhir_stack : ('freshtv373 * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position) = Obj.magic _menhir_stack in
    let (_endpos__3_ : Lexing.position) = _endpos in
    ((let ((_menhir_stack, _menhir_s, _startpos__1_), _endpos_e_, _, (e : 'tv_int_expr), _startpos_e_) = _menhir_stack in
    let _3 = () in
    let _1 = () in
    let _startpos = _startpos__1_ in
    let _endpos = _endpos__3_ in
    let _v : 'tv_int_expr = 
# 141 "frontend/parser.mly"
    ( e )
# 273 "frontend/parser.ml"
     in
    _menhir_goto_int_expr _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv374)

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

and _menhir_run27 : _menhir_env -> 'ttv_tail * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _startpos ->
    let _menhir_stack = (_menhir_stack, _startpos) in
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

and _menhir_goto_sign_int_literal : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> 'tv_sign_int_literal -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    let _menhir_stack = (_menhir_stack, _endpos, _menhir_s, _v, _startpos) in
    match _menhir_s with
    | MenhirState6 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv363 * _menhir_state * Lexing.position) * Lexing.position) * Lexing.position * _menhir_state * 'tv_sign_int_literal * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | TOK_COMMA ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv359 * _menhir_state * Lexing.position) * Lexing.position) * Lexing.position * _menhir_state * 'tv_sign_int_literal * Lexing.position) = Obj.magic _menhir_stack in
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
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState13) : 'freshtv360)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv361 * _menhir_state * Lexing.position) * Lexing.position) * Lexing.position * _menhir_state * 'tv_sign_int_literal * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv362)) : 'freshtv364)
    | MenhirState13 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (((('freshtv371 * _menhir_state * Lexing.position) * Lexing.position) * Lexing.position * _menhir_state * 'tv_sign_int_literal * Lexing.position)) * Lexing.position * _menhir_state * 'tv_sign_int_literal * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | TOK_RPAREN ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (((('freshtv367 * _menhir_state * Lexing.position) * Lexing.position) * Lexing.position * _menhir_state * 'tv_sign_int_literal * Lexing.position)) * Lexing.position * _menhir_state * 'tv_sign_int_literal * Lexing.position) = Obj.magic _menhir_stack in
            let (_endpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (((('freshtv365 * _menhir_state * Lexing.position) * Lexing.position) * Lexing.position * _menhir_state * 'tv_sign_int_literal * Lexing.position)) * Lexing.position * _menhir_state * 'tv_sign_int_literal * Lexing.position) = Obj.magic _menhir_stack in
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
              
# 215 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 408 "frontend/parser.ml"
              
            in
            let e1 =
              let _endpos_x_ = _endpos_x0_ in
              let _startpos_x_ = _startpos_x0_ in
              let x = x0 in
              let _endpos = _endpos_x_ in
              let _startpos = _startpos_x_ in
              
# 215 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 420 "frontend/parser.ml"
              
            in
            
# 157 "frontend/parser.mly"
    ( AST_rand (e1, e2) )
# 426 "frontend/parser.ml"
             in
            _menhir_goto_int_expr _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv366)) : 'freshtv368)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (((('freshtv369 * _menhir_state * Lexing.position) * Lexing.position) * Lexing.position * _menhir_state * 'tv_sign_int_literal * Lexing.position)) * Lexing.position * _menhir_state * 'tv_sign_int_literal * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv370)) : 'freshtv372)
    | _ ->
        _menhir_fail ()

and _menhir_run56 : _menhir_env -> 'ttv_tail * Lexing.position * _menhir_state * 'tv_bool_expr * Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | TOK_EXCLAIM ->
        _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState56 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_FALSE ->
        _menhir_run37 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState56 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_LPAREN ->
        _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState56 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_MINUS ->
        _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState56 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_PLUS ->
        _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState56 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_RAND ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState56 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_TRUE ->
        _menhir_run35 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState56 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_id _v ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState56 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_int _v ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState56 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState56

and _menhir_run58 : _menhir_env -> 'ttv_tail * Lexing.position * _menhir_state * 'tv_bool_expr * Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | TOK_EXCLAIM ->
        _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState58 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_FALSE ->
        _menhir_run37 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState58 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_LPAREN ->
        _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState58 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_MINUS ->
        _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState58 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_PLUS ->
        _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState58 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_RAND ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState58 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_TRUE ->
        _menhir_run35 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState58 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_id _v ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState58 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_int _v ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState58 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState58

and _menhir_goto_separated_nonempty_list_TOK_COMMA_ext_TOK_id__ : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_separated_nonempty_list_TOK_COMMA_ext_TOK_id__ -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    match _menhir_s with
    | MenhirState65 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv353 * Lexing.position * _menhir_state * (
# 54 "frontend/parser.mly"
       (string)
# 503 "frontend/parser.ml"
        ) * Lexing.position)) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : 'tv_separated_nonempty_list_TOK_COMMA_ext_TOK_id__) = _v in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv351 * Lexing.position * _menhir_state * (
# 54 "frontend/parser.mly"
       (string)
# 511 "frontend/parser.ml"
        ) * Lexing.position)) = Obj.magic _menhir_stack in
        let (_ : _menhir_state) = _menhir_s in
        let ((xs : 'tv_separated_nonempty_list_TOK_COMMA_ext_TOK_id__) : 'tv_separated_nonempty_list_TOK_COMMA_ext_TOK_id__) = _v in
        ((let (_menhir_stack, _endpos_x0_, _menhir_s, (x0 : (
# 54 "frontend/parser.mly"
       (string)
# 518 "frontend/parser.ml"
        )), _startpos_x0_) = _menhir_stack in
        let _2 = () in
        let _v : 'tv_separated_nonempty_list_TOK_COMMA_ext_TOK_id__ = let x =
          let _endpos_x_ = _endpos_x0_ in
          let _startpos_x_ = _startpos_x0_ in
          let x = x0 in
          let _endpos = _endpos_x_ in
          let _startpos = _startpos_x_ in
          
# 215 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 530 "frontend/parser.ml"
          
        in
        
# 218 "/home/tas/.opam/system/lib/menhir/standard.mly"
    ( x :: xs )
# 536 "frontend/parser.ml"
         in
        _menhir_goto_separated_nonempty_list_TOK_COMMA_ext_TOK_id__ _menhir_env _menhir_stack _menhir_s _v) : 'freshtv352)) : 'freshtv354)
    | MenhirState63 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv357) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : 'tv_separated_nonempty_list_TOK_COMMA_ext_TOK_id__) = _v in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv355) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let ((x : 'tv_separated_nonempty_list_TOK_COMMA_ext_TOK_id__) : 'tv_separated_nonempty_list_TOK_COMMA_ext_TOK_id__) = _v in
        ((let _v : 'tv_loption_separated_nonempty_list_TOK_COMMA_ext_TOK_id___ = 
# 131 "/home/tas/.opam/system/lib/menhir/standard.mly"
    ( x )
# 551 "frontend/parser.ml"
         in
        _menhir_goto_loption_separated_nonempty_list_TOK_COMMA_ext_TOK_id___ _menhir_env _menhir_stack _menhir_s _v) : 'freshtv356)) : 'freshtv358)
    | _ ->
        _menhir_fail ()

and _menhir_goto_list_ext_decl__ : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_list_ext_decl__ -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState71 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv345 * _menhir_state * Lexing.position) * _menhir_state * 'tv_list_ext_decl__) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | TOK_ASSERT ->
            _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState76 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_HALT ->
            _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState76 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_IF ->
            _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState76 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_LCURLY ->
            _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState76 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_PRINT ->
            _menhir_run62 _menhir_env (Obj.magic _menhir_stack) MenhirState76 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_WHILE ->
            _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState76 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_id _v ->
            _menhir_run1 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState76 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_RCURLY ->
            _menhir_reduce28 _menhir_env (Obj.magic _menhir_stack) MenhirState76
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState76) : 'freshtv346)
    | MenhirState96 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv349 * Lexing.position * _menhir_state * 'tv_decl * Lexing.position) * _menhir_state * 'tv_list_ext_decl__) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv347 * Lexing.position * _menhir_state * 'tv_decl * Lexing.position) * _menhir_state * 'tv_list_ext_decl__) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _endpos_x0_, _menhir_s, (x0 : 'tv_decl), _startpos_x0_), _, (xs : 'tv_list_ext_decl__)) = _menhir_stack in
        let _v : 'tv_list_ext_decl__ = let x =
          let _endpos_x_ = _endpos_x0_ in
          let _startpos_x_ = _startpos_x0_ in
          let x = x0 in
          let _endpos = _endpos_x_ in
          let _startpos = _startpos_x_ in
          
# 215 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 602 "frontend/parser.ml"
          
        in
        
# 188 "/home/tas/.opam/system/lib/menhir/standard.mly"
    ( x :: xs )
# 608 "frontend/parser.ml"
         in
        _menhir_goto_list_ext_decl__ _menhir_env _menhir_stack _menhir_s _v) : 'freshtv348)) : 'freshtv350)
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
        let (_menhir_stack : ('freshtv259 * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | TOK_DIVIDE ->
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack)
        | TOK_MINUS ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
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
            let (_menhir_stack : ('freshtv257 * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv258)) : 'freshtv260)
    | MenhirState20 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv263 * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position)) * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv261 * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position)) * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position) = Obj.magic _menhir_stack in
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
          
# 215 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 664 "frontend/parser.ml"
          
        in
        let o =
          let _1 = _10 in
          
# 97 "frontend/parser.mly"
                     ( AST_MULTIPLY )
# 672 "frontend/parser.ml"
          
        in
        let e1 =
          let _endpos_x_ = _endpos_x0_ in
          let _startpos_x_ = _startpos_x0_ in
          let x = x0 in
          let _endpos = _endpos_x_ in
          let _startpos = _startpos_x_ in
          
# 215 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 684 "frontend/parser.ml"
          
        in
        
# 153 "frontend/parser.mly"
    ( AST_int_binary (o,e1,e2) )
# 690 "frontend/parser.ml"
         in
        _menhir_goto_int_expr _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv262)) : 'freshtv264)
    | MenhirState23 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv269 * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position) * Lexing.position) * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | TOK_DIVIDE ->
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack)
        | TOK_STAR ->
            _menhir_run20 _menhir_env (Obj.magic _menhir_stack)
        | TOK_AND_AND | TOK_BAR_BAR | TOK_EQUAL_EQUAL | TOK_GREATER | TOK_GREATER_EQUAL | TOK_LESS | TOK_LESS_EQUAL | TOK_MINUS | TOK_NOT_EQUAL | TOK_PLUS | TOK_RPAREN | TOK_SEMICOLON ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv265 * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position) * Lexing.position) * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position) = Obj.magic _menhir_stack in
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
              
# 215 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 719 "frontend/parser.ml"
              
            in
            let o =
              let _1 = _10 in
              
# 99 "frontend/parser.mly"
                     ( AST_PLUS )
# 727 "frontend/parser.ml"
              
            in
            let e1 =
              let _endpos_x_ = _endpos_x0_ in
              let _startpos_x_ = _startpos_x0_ in
              let x = x0 in
              let _endpos = _endpos_x_ in
              let _startpos = _startpos_x_ in
              
# 215 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 739 "frontend/parser.ml"
              
            in
            
# 153 "frontend/parser.mly"
    ( AST_int_binary (o,e1,e2) )
# 745 "frontend/parser.ml"
             in
            _menhir_goto_int_expr _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv266)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv267 * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position) * Lexing.position) * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv268)) : 'freshtv270)
    | MenhirState25 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv273 * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position)) * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv271 * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position)) * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position) = Obj.magic _menhir_stack in
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
          
# 215 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 773 "frontend/parser.ml"
          
        in
        let o =
          let _1 = _10 in
          
# 98 "frontend/parser.mly"
                     ( AST_DIVIDE )
# 781 "frontend/parser.ml"
          
        in
        let e1 =
          let _endpos_x_ = _endpos_x0_ in
          let _startpos_x_ = _startpos_x0_ in
          let x = x0 in
          let _endpos = _endpos_x_ in
          let _startpos = _startpos_x_ in
          
# 215 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 793 "frontend/parser.ml"
          
        in
        
# 153 "frontend/parser.mly"
    ( AST_int_binary (o,e1,e2) )
# 799 "frontend/parser.ml"
         in
        _menhir_goto_int_expr _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv272)) : 'freshtv274)
    | MenhirState27 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv279 * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position) * Lexing.position) * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | TOK_DIVIDE ->
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack)
        | TOK_STAR ->
            _menhir_run20 _menhir_env (Obj.magic _menhir_stack)
        | TOK_AND_AND | TOK_BAR_BAR | TOK_EQUAL_EQUAL | TOK_GREATER | TOK_GREATER_EQUAL | TOK_LESS | TOK_LESS_EQUAL | TOK_MINUS | TOK_NOT_EQUAL | TOK_PLUS | TOK_RPAREN | TOK_SEMICOLON ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv275 * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position) * Lexing.position) * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position) = Obj.magic _menhir_stack in
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
              
# 215 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 828 "frontend/parser.ml"
              
            in
            let o =
              let _1 = _10 in
              
# 100 "frontend/parser.mly"
                     ( AST_MINUS )
# 836 "frontend/parser.ml"
              
            in
            let e1 =
              let _endpos_x_ = _endpos_x0_ in
              let _startpos_x_ = _startpos_x0_ in
              let x = x0 in
              let _endpos = _endpos_x_ in
              let _startpos = _startpos_x_ in
              
# 215 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 848 "frontend/parser.ml"
              
            in
            
# 153 "frontend/parser.mly"
    ( AST_int_binary (o,e1,e2) )
# 854 "frontend/parser.ml"
             in
            _menhir_goto_int_expr _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv276)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv277 * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position) * Lexing.position) * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv278)) : 'freshtv280)
    | MenhirState17 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv285 * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | TOK_DIVIDE ->
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack)
        | TOK_STAR ->
            _menhir_run20 _menhir_env (Obj.magic _menhir_stack)
        | TOK_AND_AND | TOK_BAR_BAR | TOK_EQUAL_EQUAL | TOK_GREATER | TOK_GREATER_EQUAL | TOK_LESS | TOK_LESS_EQUAL | TOK_MINUS | TOK_NOT_EQUAL | TOK_PLUS | TOK_RPAREN | TOK_SEMICOLON ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv281 * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position) = Obj.magic _menhir_stack in
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
              
# 215 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 890 "frontend/parser.ml"
              
            in
            let o =
              let _1 = _10 in
              
# 89 "frontend/parser.mly"
                     ( AST_UNARY_MINUS )
# 898 "frontend/parser.ml"
              
            in
            
# 150 "frontend/parser.mly"
    ( AST_int_unary (o,e) )
# 904 "frontend/parser.ml"
             in
            _menhir_goto_int_expr _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv282)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv283 * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv284)) : 'freshtv286)
    | MenhirState16 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv291 * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | TOK_DIVIDE ->
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
              
# 215 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 940 "frontend/parser.ml"
              
            in
            let o =
              let _1 = _10 in
              
# 88 "frontend/parser.mly"
                     ( AST_UNARY_PLUS )
# 948 "frontend/parser.ml"
              
            in
            
# 150 "frontend/parser.mly"
    ( AST_int_unary (o,e) )
# 954 "frontend/parser.ml"
             in
            _menhir_goto_int_expr _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv288)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv289 * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv290)) : 'freshtv292)
    | MenhirState2 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv299 * Lexing.position * _menhir_state * (
# 54 "frontend/parser.mly"
       (string)
# 969 "frontend/parser.ml"
        ) * Lexing.position)) * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | TOK_DIVIDE ->
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack)
        | TOK_MINUS ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_PLUS ->
            _menhir_run23 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_SEMICOLON ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv295 * Lexing.position * _menhir_state * (
# 54 "frontend/parser.mly"
       (string)
# 985 "frontend/parser.ml"
            ) * Lexing.position)) * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position) = Obj.magic _menhir_stack in
            let (_endpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv293 * Lexing.position * _menhir_state * (
# 54 "frontend/parser.mly"
       (string)
# 993 "frontend/parser.ml"
            ) * Lexing.position)) * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position) = Obj.magic _menhir_stack in
            let (_endpos__4_ : Lexing.position) = _endpos in
            ((let ((_menhir_stack, _endpos_x0_, _menhir_s, (x0 : (
# 54 "frontend/parser.mly"
       (string)
# 999 "frontend/parser.ml"
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
              
# 215 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 1014 "frontend/parser.ml"
              
            in
            let e =
              let _endpos_x_ = _endpos_x0_ in
              let _startpos_x_ = _startpos_x0_ in
              let x = x0 in
              let _endpos = _endpos_x_ in
              let _startpos = _startpos_x_ in
              
# 215 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 1026 "frontend/parser.ml"
              
            in
            
# 189 "frontend/parser.mly"
  ( AST_assign (e, f) )
# 1032 "frontend/parser.ml"
             in
            _menhir_goto_stat _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv294)) : 'freshtv296)
        | TOK_STAR ->
            _menhir_run20 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv297 * Lexing.position * _menhir_state * (
# 54 "frontend/parser.mly"
       (string)
# 1044 "frontend/parser.ml"
            ) * Lexing.position)) * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv298)) : 'freshtv300)
    | MenhirState84 | MenhirState78 | MenhirState34 | MenhirState58 | MenhirState56 | MenhirState38 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv303 * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | TOK_DIVIDE ->
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack)
        | TOK_EQUAL_EQUAL ->
            _menhir_run50 _menhir_env (Obj.magic _menhir_stack)
        | TOK_GREATER ->
            _menhir_run48 _menhir_env (Obj.magic _menhir_stack)
        | TOK_GREATER_EQUAL ->
            _menhir_run46 _menhir_env (Obj.magic _menhir_stack)
        | TOK_LESS ->
            _menhir_run44 _menhir_env (Obj.magic _menhir_stack)
        | TOK_LESS_EQUAL ->
            _menhir_run42 _menhir_env (Obj.magic _menhir_stack)
        | TOK_MINUS ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_NOT_EQUAL ->
            _menhir_run40 _menhir_env (Obj.magic _menhir_stack)
        | TOK_PLUS ->
            _menhir_run23 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_STAR ->
            _menhir_run20 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv301 * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv302)) : 'freshtv304)
    | MenhirState40 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv309 * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position)) * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | TOK_DIVIDE ->
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack)
        | TOK_MINUS ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_PLUS ->
            _menhir_run23 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_STAR ->
            _menhir_run20 _menhir_env (Obj.magic _menhir_stack)
        | TOK_AND_AND | TOK_BAR_BAR | TOK_RPAREN ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv305 * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position)) * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position) = Obj.magic _menhir_stack in
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
              
# 215 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 1111 "frontend/parser.ml"
              
            in
            let o =
              let _1 = _10 in
              
# 109 "frontend/parser.mly"
                     ( AST_NOT_EQUAL )
# 1119 "frontend/parser.ml"
              
            in
            let e1 =
              let _endpos_x_ = _endpos_x0_ in
              let _startpos_x_ = _startpos_x0_ in
              let x = x0 in
              let _endpos = _endpos_x_ in
              let _startpos = _startpos_x_ in
              
# 215 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 1131 "frontend/parser.ml"
              
            in
            
# 135 "frontend/parser.mly"
    ( AST_compare (o,e1,e2) )
# 1137 "frontend/parser.ml"
             in
            _menhir_goto_bool_expr _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv306)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv307 * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position)) * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv308)) : 'freshtv310)
    | MenhirState42 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv315 * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position)) * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | TOK_DIVIDE ->
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack)
        | TOK_MINUS ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
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
              
# 215 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 1177 "frontend/parser.ml"
              
            in
            let o =
              let _1 = _10 in
              
# 106 "frontend/parser.mly"
                     ( AST_LESS_EQUAL )
# 1185 "frontend/parser.ml"
              
            in
            let e1 =
              let _endpos_x_ = _endpos_x0_ in
              let _startpos_x_ = _startpos_x0_ in
              let x = x0 in
              let _endpos = _endpos_x_ in
              let _startpos = _startpos_x_ in
              
# 215 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 1197 "frontend/parser.ml"
              
            in
            
# 135 "frontend/parser.mly"
    ( AST_compare (o,e1,e2) )
# 1203 "frontend/parser.ml"
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
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack)
        | TOK_MINUS ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
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
              
# 215 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 1243 "frontend/parser.ml"
              
            in
            let o =
              let _1 = _10 in
              
# 104 "frontend/parser.mly"
                     ( AST_LESS )
# 1251 "frontend/parser.ml"
              
            in
            let e1 =
              let _endpos_x_ = _endpos_x0_ in
              let _startpos_x_ = _startpos_x0_ in
              let x = x0 in
              let _endpos = _endpos_x_ in
              let _startpos = _startpos_x_ in
              
# 215 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 1263 "frontend/parser.ml"
              
            in
            
# 135 "frontend/parser.mly"
    ( AST_compare (o,e1,e2) )
# 1269 "frontend/parser.ml"
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
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack)
        | TOK_MINUS ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
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
              
# 215 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 1309 "frontend/parser.ml"
              
            in
            let o =
              let _1 = _10 in
              
# 107 "frontend/parser.mly"
                     ( AST_GREATER_EQUAL )
# 1317 "frontend/parser.ml"
              
            in
            let e1 =
              let _endpos_x_ = _endpos_x0_ in
              let _startpos_x_ = _startpos_x0_ in
              let x = x0 in
              let _endpos = _endpos_x_ in
              let _startpos = _startpos_x_ in
              
# 215 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 1329 "frontend/parser.ml"
              
            in
            
# 135 "frontend/parser.mly"
    ( AST_compare (o,e1,e2) )
# 1335 "frontend/parser.ml"
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
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack)
        | TOK_MINUS ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
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
              
# 215 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 1375 "frontend/parser.ml"
              
            in
            let o =
              let _1 = _10 in
              
# 105 "frontend/parser.mly"
                     ( AST_GREATER )
# 1383 "frontend/parser.ml"
              
            in
            let e1 =
              let _endpos_x_ = _endpos_x0_ in
              let _startpos_x_ = _startpos_x0_ in
              let x = x0 in
              let _endpos = _endpos_x_ in
              let _startpos = _startpos_x_ in
              
# 215 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 1395 "frontend/parser.ml"
              
            in
            
# 135 "frontend/parser.mly"
    ( AST_compare (o,e1,e2) )
# 1401 "frontend/parser.ml"
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
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack)
        | TOK_MINUS ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
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
              
# 215 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 1441 "frontend/parser.ml"
              
            in
            let o =
              let _1 = _10 in
              
# 108 "frontend/parser.mly"
                     ( AST_EQUAL )
# 1449 "frontend/parser.ml"
              
            in
            let e1 =
              let _endpos_x_ = _endpos_x0_ in
              let _startpos_x_ = _startpos_x0_ in
              let x = x0 in
              let _endpos = _endpos_x_ in
              let _startpos = _startpos_x_ in
              
# 215 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 1461 "frontend/parser.ml"
              
            in
            
# 135 "frontend/parser.mly"
    ( AST_compare (o,e1,e2) )
# 1467 "frontend/parser.ml"
             in
            _menhir_goto_bool_expr _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv336)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv337 * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position)) * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv338)) : 'freshtv340)
    | MenhirState36 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv343 * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | TOK_DIVIDE ->
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack)
        | TOK_EQUAL_EQUAL ->
            _menhir_run50 _menhir_env (Obj.magic _menhir_stack)
        | TOK_GREATER ->
            _menhir_run48 _menhir_env (Obj.magic _menhir_stack)
        | TOK_GREATER_EQUAL ->
            _menhir_run46 _menhir_env (Obj.magic _menhir_stack)
        | TOK_LESS ->
            _menhir_run44 _menhir_env (Obj.magic _menhir_stack)
        | TOK_LESS_EQUAL ->
            _menhir_run42 _menhir_env (Obj.magic _menhir_stack)
        | TOK_MINUS ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_NOT_EQUAL ->
            _menhir_run40 _menhir_env (Obj.magic _menhir_stack)
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
            let (_menhir_stack : ('freshtv341 * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv342)) : 'freshtv344)
    | _ ->
        _menhir_fail ()

and _menhir_run7 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> (
# 55 "frontend/parser.mly"
       (string)
# 1518 "frontend/parser.ml"
) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    let _menhir_env = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv255) = Obj.magic _menhir_stack in
    let (_endpos_i_ : Lexing.position) = _endpos in
    let (_menhir_s : _menhir_state) = _menhir_s in
    let ((i : (
# 55 "frontend/parser.mly"
       (string)
# 1529 "frontend/parser.ml"
    )) : (
# 55 "frontend/parser.mly"
       (string)
# 1533 "frontend/parser.ml"
    )) = _v in
    let (_startpos_i_ : Lexing.position) = _startpos in
    ((let _startpos = _startpos_i_ in
    let _endpos = _endpos_i_ in
    let _v : 'tv_sign_int_literal = 
# 162 "frontend/parser.mly"
                       ( i )
# 1541 "frontend/parser.ml"
     in
    _menhir_goto_sign_int_literal _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv256)

and _menhir_run8 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | TOK_int _v ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv251 * _menhir_state * Lexing.position) = Obj.magic _menhir_stack in
        let (_endpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
        let (_v : (
# 55 "frontend/parser.mly"
       (string)
# 1558 "frontend/parser.ml"
        )) = _v in
        let (_startpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
        ((let _menhir_env = _menhir_discard _menhir_env in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv249 * _menhir_state * Lexing.position) = Obj.magic _menhir_stack in
        let (_endpos_i_ : Lexing.position) = _endpos in
        let ((i : (
# 55 "frontend/parser.mly"
       (string)
# 1568 "frontend/parser.ml"
        )) : (
# 55 "frontend/parser.mly"
       (string)
# 1572 "frontend/parser.ml"
        )) = _v in
        let (_startpos_i_ : Lexing.position) = _startpos in
        ((let (_menhir_stack, _menhir_s, _startpos__1_) = _menhir_stack in
        let _1 = () in
        let _startpos = _startpos__1_ in
        let _endpos = _endpos_i_ in
        let _v : 'tv_sign_int_literal = 
# 163 "frontend/parser.mly"
                       ( i )
# 1582 "frontend/parser.ml"
         in
        _menhir_goto_sign_int_literal _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv250)) : 'freshtv252)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv253 * _menhir_state * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv254)

and _menhir_run10 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | TOK_int _v ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv245 * _menhir_state * Lexing.position) = Obj.magic _menhir_stack in
        let (_endpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
        let (_v : (
# 55 "frontend/parser.mly"
       (string)
# 1606 "frontend/parser.ml"
        )) = _v in
        let (_startpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
        ((let _menhir_env = _menhir_discard _menhir_env in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv243 * _menhir_state * Lexing.position) = Obj.magic _menhir_stack in
        let (_endpos_i_ : Lexing.position) = _endpos in
        let ((i : (
# 55 "frontend/parser.mly"
       (string)
# 1616 "frontend/parser.ml"
        )) : (
# 55 "frontend/parser.mly"
       (string)
# 1620 "frontend/parser.ml"
        )) = _v in
        let (_startpos_i_ : Lexing.position) = _startpos in
        ((let (_menhir_stack, _menhir_s, _startpos__1_) = _menhir_stack in
        let _1 = () in
        let _startpos = _startpos__1_ in
        let _endpos = _endpos_i_ in
        let _v : 'tv_sign_int_literal = 
# 164 "frontend/parser.mly"
                       ( "-"^i )
# 1630 "frontend/parser.ml"
         in
        _menhir_goto_sign_int_literal _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv244)) : 'freshtv246)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv247 * _menhir_state * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv248)

and _menhir_goto_bool_expr : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> 'tv_bool_expr -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    let _menhir_stack = (_menhir_stack, _endpos, _menhir_s, _v, _startpos) in
    match _menhir_s with
    | MenhirState38 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv199 * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_bool_expr * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv197 * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_bool_expr * Lexing.position) = Obj.magic _menhir_stack in
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
          
# 215 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 1663 "frontend/parser.ml"
          
        in
        let o =
          let _1 = _10 in
          
# 93 "frontend/parser.mly"
                     ( AST_NOT )
# 1671 "frontend/parser.ml"
          
        in
        
# 129 "frontend/parser.mly"
    ( AST_bool_unary (o,e) )
# 1677 "frontend/parser.ml"
         in
        _menhir_goto_bool_expr _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv198)) : 'freshtv200)
    | MenhirState36 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv207 * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_bool_expr * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | TOK_AND_AND ->
            _menhir_run58 _menhir_env (Obj.magic _menhir_stack)
        | TOK_BAR_BAR ->
            _menhir_run56 _menhir_env (Obj.magic _menhir_stack)
        | TOK_RPAREN ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv203 * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_bool_expr * Lexing.position) = Obj.magic _menhir_stack in
            let (_endpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv201 * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_bool_expr * Lexing.position) = Obj.magic _menhir_stack in
            let (_endpos__3_ : Lexing.position) = _endpos in
            ((let ((_menhir_stack, _menhir_s, _startpos__1_), _endpos_e_, _, (e : 'tv_bool_expr), _startpos_e_) = _menhir_stack in
            let _3 = () in
            let _1 = () in
            let _startpos = _startpos__1_ in
            let _endpos = _endpos__3_ in
            let _v : 'tv_bool_expr = 
# 120 "frontend/parser.mly"
    ( e )
# 1706 "frontend/parser.ml"
             in
            _menhir_goto_bool_expr _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv202)) : 'freshtv204)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv205 * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_bool_expr * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv206)) : 'freshtv208)
    | MenhirState56 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv213 * Lexing.position * _menhir_state * 'tv_bool_expr * Lexing.position)) * Lexing.position * _menhir_state * 'tv_bool_expr * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | TOK_AND_AND ->
            _menhir_run58 _menhir_env (Obj.magic _menhir_stack)
        | TOK_BAR_BAR | TOK_RPAREN ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv209 * Lexing.position * _menhir_state * 'tv_bool_expr * Lexing.position)) * Lexing.position * _menhir_state * 'tv_bool_expr * Lexing.position) = Obj.magic _menhir_stack in
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
              
# 215 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 1740 "frontend/parser.ml"
              
            in
            let o =
              let _1 = _10 in
              
# 114 "frontend/parser.mly"
                     ( AST_OR )
# 1748 "frontend/parser.ml"
              
            in
            let e1 =
              let _endpos_x_ = _endpos_x0_ in
              let _startpos_x_ = _startpos_x0_ in
              let x = x0 in
              let _endpos = _endpos_x_ in
              let _startpos = _startpos_x_ in
              
# 215 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 1760 "frontend/parser.ml"
              
            in
            
# 132 "frontend/parser.mly"
    ( AST_bool_binary (o,e1,e2) )
# 1766 "frontend/parser.ml"
             in
            _menhir_goto_bool_expr _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv210)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv211 * Lexing.position * _menhir_state * 'tv_bool_expr * Lexing.position)) * Lexing.position * _menhir_state * 'tv_bool_expr * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv212)) : 'freshtv214)
    | MenhirState58 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv217 * Lexing.position * _menhir_state * 'tv_bool_expr * Lexing.position)) * Lexing.position * _menhir_state * 'tv_bool_expr * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv215 * Lexing.position * _menhir_state * 'tv_bool_expr * Lexing.position)) * Lexing.position * _menhir_state * 'tv_bool_expr * Lexing.position) = Obj.magic _menhir_stack in
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
          
# 215 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 1794 "frontend/parser.ml"
          
        in
        let o =
          let _1 = _10 in
          
# 113 "frontend/parser.mly"
                     ( AST_AND )
# 1802 "frontend/parser.ml"
          
        in
        let e1 =
          let _endpos_x_ = _endpos_x0_ in
          let _startpos_x_ = _startpos_x0_ in
          let x = x0 in
          let _endpos = _endpos_x_ in
          let _startpos = _startpos_x_ in
          
# 215 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 1814 "frontend/parser.ml"
          
        in
        
# 132 "frontend/parser.mly"
    ( AST_bool_binary (o,e1,e2) )
# 1820 "frontend/parser.ml"
         in
        _menhir_goto_bool_expr _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv216)) : 'freshtv218)
    | MenhirState34 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv223 * _menhir_state * Lexing.position) * Lexing.position) * Lexing.position * _menhir_state * 'tv_bool_expr * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | TOK_AND_AND ->
            _menhir_run58 _menhir_env (Obj.magic _menhir_stack)
        | TOK_BAR_BAR ->
            _menhir_run56 _menhir_env (Obj.magic _menhir_stack)
        | TOK_RPAREN ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv219 * _menhir_state * Lexing.position) * Lexing.position) * Lexing.position * _menhir_state * 'tv_bool_expr * Lexing.position) = Obj.magic _menhir_stack in
            let (_endpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            ((let _menhir_stack = (_menhir_stack, _endpos) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | TOK_ASSERT ->
                _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState61 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TOK_HALT ->
                _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState61 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TOK_IF ->
                _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState61 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TOK_LCURLY ->
                _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState61 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TOK_PRINT ->
                _menhir_run62 _menhir_env (Obj.magic _menhir_stack) MenhirState61 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TOK_WHILE ->
                _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState61 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TOK_id _v ->
                _menhir_run1 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState61 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState61) : 'freshtv220)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv221 * _menhir_state * Lexing.position) * Lexing.position) * Lexing.position * _menhir_state * 'tv_bool_expr * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv222)) : 'freshtv224)
    | MenhirState78 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv229 * _menhir_state * Lexing.position) * Lexing.position) * Lexing.position * _menhir_state * 'tv_bool_expr * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | TOK_AND_AND ->
            _menhir_run58 _menhir_env (Obj.magic _menhir_stack)
        | TOK_BAR_BAR ->
            _menhir_run56 _menhir_env (Obj.magic _menhir_stack)
        | TOK_RPAREN ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv225 * _menhir_state * Lexing.position) * Lexing.position) * Lexing.position * _menhir_state * 'tv_bool_expr * Lexing.position) = Obj.magic _menhir_stack in
            let (_endpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            ((let _menhir_stack = (_menhir_stack, _endpos) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | TOK_ASSERT ->
                _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState80 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TOK_HALT ->
                _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState80 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TOK_IF ->
                _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState80 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TOK_LCURLY ->
                _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState80 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TOK_PRINT ->
                _menhir_run62 _menhir_env (Obj.magic _menhir_stack) MenhirState80 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TOK_WHILE ->
                _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState80 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TOK_id _v ->
                _menhir_run1 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState80 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState80) : 'freshtv226)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv227 * _menhir_state * Lexing.position) * Lexing.position) * Lexing.position * _menhir_state * 'tv_bool_expr * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv228)) : 'freshtv230)
    | MenhirState84 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv241 * _menhir_state * Lexing.position) * Lexing.position) * Lexing.position * _menhir_state * 'tv_bool_expr * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | TOK_AND_AND ->
            _menhir_run58 _menhir_env (Obj.magic _menhir_stack)
        | TOK_BAR_BAR ->
            _menhir_run56 _menhir_env (Obj.magic _menhir_stack)
        | TOK_RPAREN ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv237 * _menhir_state * Lexing.position) * Lexing.position) * Lexing.position * _menhir_state * 'tv_bool_expr * Lexing.position) = Obj.magic _menhir_stack in
            let (_endpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            ((let _menhir_stack = (_menhir_stack, _endpos) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | TOK_SEMICOLON ->
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : ((('freshtv233 * _menhir_state * Lexing.position) * Lexing.position) * Lexing.position * _menhir_state * 'tv_bool_expr * Lexing.position) * Lexing.position) = Obj.magic _menhir_stack in
                let (_endpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
                ((let _menhir_env = _menhir_discard _menhir_env in
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : ((('freshtv231 * _menhir_state * Lexing.position) * Lexing.position) * Lexing.position * _menhir_state * 'tv_bool_expr * Lexing.position) * Lexing.position) = Obj.magic _menhir_stack in
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
                  
# 215 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 1951 "frontend/parser.ml"
                  
                in
                
# 201 "frontend/parser.mly"
  ( AST_assert e )
# 1957 "frontend/parser.ml"
                 in
                _menhir_goto_stat _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv232)) : 'freshtv234)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : ((('freshtv235 * _menhir_state * Lexing.position) * Lexing.position) * Lexing.position * _menhir_state * 'tv_bool_expr * Lexing.position) * Lexing.position) = Obj.magic _menhir_stack in
                ((let ((_menhir_stack, _, _menhir_s, _, _), _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv236)) : 'freshtv238)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv239 * _menhir_state * Lexing.position) * Lexing.position) * Lexing.position * _menhir_state * 'tv_bool_expr * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv240)) : 'freshtv242)
    | _ ->
        _menhir_fail ()

and _menhir_goto_list_ext_stat__ : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_list_ext_stat__ -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState92 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv167 * Lexing.position * _menhir_state * 'tv_stat * Lexing.position) * _menhir_state * 'tv_list_ext_stat__) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv165 * Lexing.position * _menhir_state * 'tv_stat * Lexing.position) * _menhir_state * 'tv_list_ext_stat__) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _endpos_x0_, _menhir_s, (x0 : 'tv_stat), _startpos_x0_), _, (xs : 'tv_list_ext_stat__)) = _menhir_stack in
        let _v : 'tv_list_ext_stat__ = let x =
          let _endpos_x_ = _endpos_x0_ in
          let _startpos_x_ = _startpos_x0_ in
          let x = x0 in
          let _endpos = _endpos_x_ in
          let _startpos = _startpos_x_ in
          
# 215 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 1996 "frontend/parser.ml"
          
        in
        
# 188 "/home/tas/.opam/system/lib/menhir/standard.mly"
    ( x :: xs )
# 2002 "frontend/parser.ml"
         in
        _menhir_goto_list_ext_stat__ _menhir_env _menhir_stack _menhir_s _v) : 'freshtv166)) : 'freshtv168)
    | MenhirState76 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv181 * _menhir_state * Lexing.position) * _menhir_state * 'tv_list_ext_decl__) * _menhir_state * 'tv_list_ext_stat__) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | TOK_RCURLY ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv177 * _menhir_state * Lexing.position) * _menhir_state * 'tv_list_ext_decl__) * _menhir_state * 'tv_list_ext_stat__) = Obj.magic _menhir_stack in
            let (_endpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv175 * _menhir_state * Lexing.position) * _menhir_state * 'tv_list_ext_decl__) * _menhir_state * 'tv_list_ext_stat__) = Obj.magic _menhir_stack in
            let (_endpos__4_ : Lexing.position) = _endpos in
            ((let (((_menhir_stack, _menhir_s, _startpos__1_), _, (d : 'tv_list_ext_decl__)), _, (l : 'tv_list_ext_stat__)) = _menhir_stack in
            let _4 = () in
            let _1 = () in
            let _startpos = _startpos__1_ in
            let _endpos = _endpos__4_ in
            let _v : 'tv_block = 
# 173 "frontend/parser.mly"
                                                             ( d, l )
# 2027 "frontend/parser.ml"
             in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv173) = _menhir_stack in
            let (_endpos : Lexing.position) = _endpos in
            let (_menhir_s : _menhir_state) = _menhir_s in
            let (_v : 'tv_block) = _v in
            let (_startpos : Lexing.position) = _startpos in
            ((let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv171) = Obj.magic _menhir_stack in
            let (_endpos : Lexing.position) = _endpos in
            let (_menhir_s : _menhir_state) = _menhir_s in
            let (_v : 'tv_block) = _v in
            let (_startpos : Lexing.position) = _startpos in
            ((let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv169) = Obj.magic _menhir_stack in
            let (_endpos_l_ : Lexing.position) = _endpos in
            let (_menhir_s : _menhir_state) = _menhir_s in
            let ((l : 'tv_block) : 'tv_block) = _v in
            let (_startpos_l_ : Lexing.position) = _startpos in
            ((let _startpos = _startpos_l_ in
            let _endpos = _endpos_l_ in
            let _v : 'tv_stat = 
# 186 "frontend/parser.mly"
  ( AST_block (fst l, snd l) )
# 2052 "frontend/parser.ml"
             in
            _menhir_goto_stat _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv170)) : 'freshtv172)) : 'freshtv174)) : 'freshtv176)) : 'freshtv178)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv179 * _menhir_state * Lexing.position) * _menhir_state * 'tv_list_ext_decl__) * _menhir_state * 'tv_list_ext_stat__) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv180)) : 'freshtv182)
    | MenhirState0 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv195 * _menhir_state * 'tv_list_ext_stat__) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | TOK_EOF ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv191 * _menhir_state * 'tv_list_ext_stat__) = Obj.magic _menhir_stack in
            ((let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv189 * _menhir_state * 'tv_list_ext_stat__) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, (t : 'tv_list_ext_stat__)) = _menhir_stack in
            let _2 = () in
            let _v : (
# 70 "frontend/parser.mly"
      (Abstract_syntax_tree.prog)
# 2078 "frontend/parser.ml"
            ) = 
# 79 "frontend/parser.mly"
                                ( t )
# 2082 "frontend/parser.ml"
             in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv187) = _menhir_stack in
            let (_menhir_s : _menhir_state) = _menhir_s in
            let (_v : (
# 70 "frontend/parser.mly"
      (Abstract_syntax_tree.prog)
# 2090 "frontend/parser.ml"
            )) = _v in
            ((let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv185) = Obj.magic _menhir_stack in
            let (_menhir_s : _menhir_state) = _menhir_s in
            let (_v : (
# 70 "frontend/parser.mly"
      (Abstract_syntax_tree.prog)
# 2098 "frontend/parser.ml"
            )) = _v in
            ((let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv183) = Obj.magic _menhir_stack in
            let (_menhir_s : _menhir_state) = _menhir_s in
            let ((_1 : (
# 70 "frontend/parser.mly"
      (Abstract_syntax_tree.prog)
# 2106 "frontend/parser.ml"
            )) : (
# 70 "frontend/parser.mly"
      (Abstract_syntax_tree.prog)
# 2110 "frontend/parser.ml"
            )) = _v in
            (Obj.magic _1 : 'freshtv184)) : 'freshtv186)) : 'freshtv188)) : 'freshtv190)) : 'freshtv192)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv193 * _menhir_state * 'tv_list_ext_stat__) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv194)) : 'freshtv196)
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
    let (_menhir_stack : (('freshtv163 * _menhir_state * Lexing.position) * Lexing.position) * _menhir_state * 'tv_loption_separated_nonempty_list_TOK_COMMA_ext_TOK_id___) = Obj.magic _menhir_stack in
    ((assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | TOK_RPAREN ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv159 * _menhir_state * Lexing.position) * Lexing.position) * _menhir_state * 'tv_loption_separated_nonempty_list_TOK_COMMA_ext_TOK_id___) = Obj.magic _menhir_stack in
        let (_endpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
        ((let _menhir_stack = (_menhir_stack, _endpos) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | TOK_SEMICOLON ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv155 * _menhir_state * Lexing.position) * Lexing.position) * _menhir_state * 'tv_loption_separated_nonempty_list_TOK_COMMA_ext_TOK_id___) * Lexing.position) = Obj.magic _menhir_stack in
            let (_endpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv153 * _menhir_state * Lexing.position) * Lexing.position) * _menhir_state * 'tv_loption_separated_nonempty_list_TOK_COMMA_ext_TOK_id___) * Lexing.position) = Obj.magic _menhir_stack in
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
# 2182 "frontend/parser.ml"
              
            in
            
# 204 "frontend/parser.mly"
  ( AST_print l )
# 2188 "frontend/parser.ml"
             in
            _menhir_goto_stat _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv154)) : 'freshtv156)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv157 * _menhir_state * Lexing.position) * Lexing.position) * _menhir_state * 'tv_loption_separated_nonempty_list_TOK_COMMA_ext_TOK_id___) * Lexing.position) = Obj.magic _menhir_stack in
            ((let ((_menhir_stack, _menhir_s, _), _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv158)) : 'freshtv160)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv161 * _menhir_state * Lexing.position) * Lexing.position) * _menhir_state * 'tv_loption_separated_nonempty_list_TOK_COMMA_ext_TOK_id___) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv162)) : 'freshtv164)

and _menhir_run64 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> (
# 54 "frontend/parser.mly"
       (string)
# 2209 "frontend/parser.ml"
) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    let _menhir_stack = (_menhir_stack, _endpos, _menhir_s, _v, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | TOK_COMMA ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv147 * Lexing.position * _menhir_state * (
# 54 "frontend/parser.mly"
       (string)
# 2221 "frontend/parser.ml"
        ) * Lexing.position) = Obj.magic _menhir_stack in
        ((let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | TOK_id _v ->
            _menhir_run64 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState65 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState65) : 'freshtv148)
    | TOK_RPAREN ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv149 * Lexing.position * _menhir_state * (
# 54 "frontend/parser.mly"
       (string)
# 2237 "frontend/parser.ml"
        ) * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _endpos_x0_, _menhir_s, (x0 : (
# 54 "frontend/parser.mly"
       (string)
# 2242 "frontend/parser.ml"
        )), _startpos_x0_) = _menhir_stack in
        let _v : 'tv_separated_nonempty_list_TOK_COMMA_ext_TOK_id__ = let x =
          let _endpos_x_ = _endpos_x0_ in
          let _startpos_x_ = _startpos_x0_ in
          let x = x0 in
          let _endpos = _endpos_x_ in
          let _startpos = _startpos_x_ in
          
# 215 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 2253 "frontend/parser.ml"
          
        in
        
# 216 "/home/tas/.opam/system/lib/menhir/standard.mly"
    ( [ x ] )
# 2259 "frontend/parser.ml"
         in
        _menhir_goto_separated_nonempty_list_TOK_COMMA_ext_TOK_id__ _menhir_env _menhir_stack _menhir_s _v) : 'freshtv150)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv151 * Lexing.position * _menhir_state * (
# 54 "frontend/parser.mly"
       (string)
# 2269 "frontend/parser.ml"
        ) * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv152)

and _menhir_reduce26 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _v : 'tv_list_ext_decl__ = 
# 186 "/home/tas/.opam/system/lib/menhir/standard.mly"
    ( [] )
# 2279 "frontend/parser.ml"
     in
    _menhir_goto_list_ext_decl__ _menhir_env _menhir_stack _menhir_s _v

and _menhir_run72 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_env = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv145) = Obj.magic _menhir_stack in
    let (_menhir_s : _menhir_state) = _menhir_s in
    let (_startpos__1_ : Lexing.position) = _startpos in
    ((let _1 = () in
    let _startpos = _startpos__1_ in
    let _v : 'tv_typ = 
# 181 "frontend/parser.mly"
          ( AST_INT )
# 2295 "frontend/parser.ml"
     in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv143) = _menhir_stack in
    let (_menhir_s : _menhir_state) = _menhir_s in
    let (_v : 'tv_typ) = _v in
    let (_startpos : Lexing.position) = _startpos in
    ((let _menhir_stack = (_menhir_stack, _menhir_s, _v, _startpos) in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv141 * _menhir_state * 'tv_typ * Lexing.position) = Obj.magic _menhir_stack in
    ((assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | TOK_id _v ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv137 * _menhir_state * 'tv_typ * Lexing.position) = Obj.magic _menhir_stack in
        let (_endpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
        let (_v : (
# 54 "frontend/parser.mly"
       (string)
# 2315 "frontend/parser.ml"
        )) = _v in
        let (_startpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
        ((let _menhir_stack = (_menhir_stack, _endpos, _v, _startpos) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | TOK_SEMICOLON ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv133 * _menhir_state * 'tv_typ * Lexing.position) * Lexing.position * (
# 54 "frontend/parser.mly"
       (string)
# 2327 "frontend/parser.ml"
            ) * Lexing.position) = Obj.magic _menhir_stack in
            let (_endpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv131 * _menhir_state * 'tv_typ * Lexing.position) * Lexing.position * (
# 54 "frontend/parser.mly"
       (string)
# 2335 "frontend/parser.ml"
            ) * Lexing.position) = Obj.magic _menhir_stack in
            let (_endpos__3_ : Lexing.position) = _endpos in
            ((let ((_menhir_stack, _menhir_s, (t : 'tv_typ), _startpos_t_), _endpos_v_, (v : (
# 54 "frontend/parser.mly"
       (string)
# 2341 "frontend/parser.ml"
            )), _startpos_v_) = _menhir_stack in
            let _3 = () in
            let _startpos = _startpos_t_ in
            let _endpos = _endpos__3_ in
            let _v : 'tv_decl = 
# 177 "frontend/parser.mly"
                               ( t, v )
# 2349 "frontend/parser.ml"
             in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv129) = _menhir_stack in
            let (_endpos : Lexing.position) = _endpos in
            let (_menhir_s : _menhir_state) = _menhir_s in
            let (_v : 'tv_decl) = _v in
            let (_startpos : Lexing.position) = _startpos in
            ((let _menhir_stack = (_menhir_stack, _endpos, _menhir_s, _v, _startpos) in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv127 * Lexing.position * _menhir_state * 'tv_decl * Lexing.position) = Obj.magic _menhir_stack in
            ((assert (not _menhir_env._menhir_error);
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | TOK_INT ->
                _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState96 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TOK_ASSERT | TOK_HALT | TOK_IF | TOK_LCURLY | TOK_PRINT | TOK_RCURLY | TOK_WHILE | TOK_id _ ->
                _menhir_reduce26 _menhir_env (Obj.magic _menhir_stack) MenhirState96
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState96) : 'freshtv128)) : 'freshtv130)) : 'freshtv132)) : 'freshtv134)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv135 * _menhir_state * 'tv_typ * Lexing.position) * Lexing.position * (
# 54 "frontend/parser.mly"
       (string)
# 2378 "frontend/parser.ml"
            ) * Lexing.position) = Obj.magic _menhir_stack in
            ((let ((_menhir_stack, _menhir_s, _, _), _, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv136)) : 'freshtv138)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv139 * _menhir_state * 'tv_typ * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv140)) : 'freshtv142)) : 'freshtv144)) : 'freshtv146)

and _menhir_goto_stat : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> 'tv_stat -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    let _menhir_stack = (_menhir_stack, _endpos, _menhir_s, _v, _startpos) in
    match _menhir_s with
    | MenhirState80 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (((('freshtv115 * _menhir_state * Lexing.position) * Lexing.position) * Lexing.position * _menhir_state * 'tv_bool_expr * Lexing.position) * Lexing.position) * Lexing.position * _menhir_state * 'tv_stat * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | TOK_ELSE ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (((('freshtv109 * _menhir_state * Lexing.position) * Lexing.position) * Lexing.position * _menhir_state * 'tv_bool_expr * Lexing.position) * Lexing.position) * Lexing.position * _menhir_state * 'tv_stat * Lexing.position) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | TOK_ASSERT ->
                _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState89 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TOK_HALT ->
                _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState89 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TOK_IF ->
                _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState89 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TOK_LCURLY ->
                _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState89 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TOK_PRINT ->
                _menhir_run62 _menhir_env (Obj.magic _menhir_stack) MenhirState89 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TOK_WHILE ->
                _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState89 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | TOK_id _v ->
                _menhir_run1 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState89 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState89) : 'freshtv110)
        | TOK_ASSERT | TOK_EOF | TOK_HALT | TOK_IF | TOK_LCURLY | TOK_PRINT | TOK_RCURLY | TOK_WHILE | TOK_id _ ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (((('freshtv111 * _menhir_state * Lexing.position) * Lexing.position) * Lexing.position * _menhir_state * 'tv_bool_expr * Lexing.position) * Lexing.position) * Lexing.position * _menhir_state * 'tv_stat * Lexing.position) = Obj.magic _menhir_stack in
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
              
# 215 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 2442 "frontend/parser.ml"
              
            in
            let e =
              let _endpos_x_ = _endpos_x0_ in
              let _startpos_x_ = _startpos_x0_ in
              let x = x0 in
              let _endpos = _endpos_x_ in
              let _startpos = _startpos_x_ in
              
# 215 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 2454 "frontend/parser.ml"
              
            in
            
# 192 "frontend/parser.mly"
  ( AST_if (e, s, None) )
# 2460 "frontend/parser.ml"
             in
            _menhir_goto_stat _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv112)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (((('freshtv113 * _menhir_state * Lexing.position) * Lexing.position) * Lexing.position * _menhir_state * 'tv_bool_expr * Lexing.position) * Lexing.position) * Lexing.position * _menhir_state * 'tv_stat * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv114)) : 'freshtv116)
    | MenhirState89 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (((((('freshtv119 * _menhir_state * Lexing.position) * Lexing.position) * Lexing.position * _menhir_state * 'tv_bool_expr * Lexing.position) * Lexing.position) * Lexing.position * _menhir_state * 'tv_stat * Lexing.position)) * Lexing.position * _menhir_state * 'tv_stat * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (((((('freshtv117 * _menhir_state * Lexing.position) * Lexing.position) * Lexing.position * _menhir_state * 'tv_bool_expr * Lexing.position) * Lexing.position) * Lexing.position * _menhir_state * 'tv_stat * Lexing.position)) * Lexing.position * _menhir_state * 'tv_stat * Lexing.position) = Obj.magic _menhir_stack in
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
          
# 215 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 2491 "frontend/parser.ml"
          
        in
        let s =
          let _endpos_x_ = _endpos_x1_ in
          let _startpos_x_ = _startpos_x1_ in
          let x = x1 in
          let _endpos = _endpos_x_ in
          let _startpos = _startpos_x_ in
          
# 215 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 2503 "frontend/parser.ml"
          
        in
        let e =
          let _endpos_x_ = _endpos_x0_ in
          let _startpos_x_ = _startpos_x0_ in
          let x = x0 in
          let _endpos = _endpos_x_ in
          let _startpos = _startpos_x_ in
          
# 215 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 2515 "frontend/parser.ml"
          
        in
        
# 195 "frontend/parser.mly"
  ( AST_if (e, s, Some t) )
# 2521 "frontend/parser.ml"
         in
        _menhir_goto_stat _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv118)) : 'freshtv120)
    | MenhirState0 | MenhirState92 | MenhirState76 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv121 * Lexing.position * _menhir_state * 'tv_stat * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | TOK_ASSERT ->
            _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState92 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_HALT ->
            _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState92 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_IF ->
            _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState92 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_LCURLY ->
            _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState92 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_PRINT ->
            _menhir_run62 _menhir_env (Obj.magic _menhir_stack) MenhirState92 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_WHILE ->
            _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState92 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_id _v ->
            _menhir_run1 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState92 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_EOF | TOK_RCURLY ->
            _menhir_reduce28 _menhir_env (Obj.magic _menhir_stack) MenhirState92
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState92) : 'freshtv122)
    | MenhirState61 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (((('freshtv125 * _menhir_state * Lexing.position) * Lexing.position) * Lexing.position * _menhir_state * 'tv_bool_expr * Lexing.position) * Lexing.position) * Lexing.position * _menhir_state * 'tv_stat * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (((('freshtv123 * _menhir_state * Lexing.position) * Lexing.position) * Lexing.position * _menhir_state * 'tv_bool_expr * Lexing.position) * Lexing.position) * Lexing.position * _menhir_state * 'tv_stat * Lexing.position) = Obj.magic _menhir_stack in
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
          
# 215 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 2570 "frontend/parser.ml"
          
        in
        let e =
          let _endpos_x_ = _endpos_x0_ in
          let _startpos_x_ = _startpos_x0_ in
          let x = x0 in
          let _endpos = _endpos_x_ in
          let _startpos = _startpos_x_ in
          
# 215 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 2582 "frontend/parser.ml"
          
        in
        
# 198 "frontend/parser.mly"
  ( AST_while (e, s) )
# 2588 "frontend/parser.ml"
         in
        _menhir_goto_stat _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv124)) : 'freshtv126)
    | _ ->
        _menhir_fail ()

and _menhir_run3 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> (
# 55 "frontend/parser.mly"
       (string)
# 2597 "frontend/parser.ml"
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
# 2608 "frontend/parser.ml"
    )) : (
# 55 "frontend/parser.mly"
       (string)
# 2612 "frontend/parser.ml"
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
      
# 215 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 2626 "frontend/parser.ml"
      
    in
    
# 144 "frontend/parser.mly"
    ( AST_int_const e )
# 2632 "frontend/parser.ml"
     in
    _menhir_goto_int_expr _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv108)

and _menhir_run4 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> (
# 54 "frontend/parser.mly"
       (string)
# 2639 "frontend/parser.ml"
) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    let _menhir_env = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv105) = Obj.magic _menhir_stack in
    let (_endpos_x0_ : Lexing.position) = _endpos in
    let (_menhir_s : _menhir_state) = _menhir_s in
    let ((x0 : (
# 54 "frontend/parser.mly"
       (string)
# 2650 "frontend/parser.ml"
    )) : (
# 54 "frontend/parser.mly"
       (string)
# 2654 "frontend/parser.ml"
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
      
# 215 "frontend/parser.mly"
      ( x, (_startpos, _endpos) )
# 2668 "frontend/parser.ml"
      
    in
    
# 147 "frontend/parser.mly"
    ( AST_identifier e )
# 2674 "frontend/parser.ml"
     in
    _menhir_goto_int_expr _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv106)

and _menhir_run35 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _startpos ->
    let _menhir_env = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv103) = Obj.magic _menhir_stack in
    let (_endpos__1_ : Lexing.position) = _endpos in
    let (_menhir_s : _menhir_state) = _menhir_s in
    let (_startpos__1_ : Lexing.position) = _startpos in
    ((let _1 = () in
    let _startpos = _startpos__1_ in
    let _endpos = _endpos__1_ in
    let _v : 'tv_bool_expr = 
# 123 "frontend/parser.mly"
    ( AST_bool_const true )
# 2692 "frontend/parser.ml"
     in
    _menhir_goto_bool_expr _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv104)

and _menhir_run5 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | TOK_LPAREN ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv99 * _menhir_state * Lexing.position) = Obj.magic _menhir_stack in
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
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState6) : 'freshtv100)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv101 * _menhir_state * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv102)

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

and _menhir_run36 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | TOK_EXCLAIM ->
        _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState36 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_FALSE ->
        _menhir_run37 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState36 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_LPAREN ->
        _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState36 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_MINUS ->
        _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState36 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_PLUS ->
        _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState36 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_RAND ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState36 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_TRUE ->
        _menhir_run35 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState36 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_id _v ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState36 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_int _v ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState36 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState36

and _menhir_run37 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _startpos ->
    let _menhir_env = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv97) = Obj.magic _menhir_stack in
    let (_endpos__1_ : Lexing.position) = _endpos in
    let (_menhir_s : _menhir_state) = _menhir_s in
    let (_startpos__1_ : Lexing.position) = _startpos in
    ((let _1 = () in
    let _startpos = _startpos__1_ in
    let _endpos = _endpos__1_ in
    let _v : 'tv_bool_expr = 
# 126 "frontend/parser.mly"
    ( AST_bool_const false )
# 2817 "frontend/parser.ml"
     in
    _menhir_goto_bool_expr _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv98)

and _menhir_run38 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | TOK_EXCLAIM ->
        _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState38 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_FALSE ->
        _menhir_run37 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState38 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_LPAREN ->
        _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState38 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_MINUS ->
        _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState38 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_PLUS ->
        _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState38 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_RAND ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState38 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_TRUE ->
        _menhir_run35 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState38 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_id _v ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState38 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_int _v ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState38 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState38

and _menhir_errorcase : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    match _menhir_s with
    | MenhirState96 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv31 * Lexing.position * _menhir_state * 'tv_decl * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv32)
    | MenhirState92 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv33 * Lexing.position * _menhir_state * 'tv_stat * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv34)
    | MenhirState89 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((((('freshtv35 * _menhir_state * Lexing.position) * Lexing.position) * Lexing.position * _menhir_state * 'tv_bool_expr * Lexing.position) * Lexing.position) * Lexing.position * _menhir_state * 'tv_stat * Lexing.position)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv36)
    | MenhirState84 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv37 * _menhir_state * Lexing.position) * Lexing.position) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv38)
    | MenhirState80 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv39 * _menhir_state * Lexing.position) * Lexing.position) * Lexing.position * _menhir_state * 'tv_bool_expr * Lexing.position) * Lexing.position) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _, _menhir_s, _, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv40)
    | MenhirState78 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv41 * _menhir_state * Lexing.position) * Lexing.position) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv42)
    | MenhirState76 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv43 * _menhir_state * Lexing.position) * _menhir_state * 'tv_list_ext_decl__) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv44)
    | MenhirState71 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv45 * _menhir_state * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv46)
    | MenhirState65 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv47 * Lexing.position * _menhir_state * (
# 54 "frontend/parser.mly"
       (string)
# 2898 "frontend/parser.ml"
        ) * Lexing.position)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv48)
    | MenhirState63 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv49 * _menhir_state * Lexing.position) * Lexing.position) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv50)
    | MenhirState61 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv51 * _menhir_state * Lexing.position) * Lexing.position) * Lexing.position * _menhir_state * 'tv_bool_expr * Lexing.position) * Lexing.position) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _, _menhir_s, _, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv52)
    | MenhirState58 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv53 * Lexing.position * _menhir_state * 'tv_bool_expr * Lexing.position)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv54)
    | MenhirState56 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv55 * Lexing.position * _menhir_state * 'tv_bool_expr * Lexing.position)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv56)
    | MenhirState50 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv57 * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv58)
    | MenhirState48 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv59 * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv60)
    | MenhirState46 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv61 * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv62)
    | MenhirState44 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv63 * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv64)
    | MenhirState42 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv65 * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv66)
    | MenhirState40 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv67 * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv68)
    | MenhirState38 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv69 * _menhir_state * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv70)
    | MenhirState36 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv71 * _menhir_state * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv72)
    | MenhirState34 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv73 * _menhir_state * Lexing.position) * Lexing.position) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv74)
    | MenhirState27 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv75 * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position) * Lexing.position) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _, _menhir_s, _, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv76)
    | MenhirState25 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv77 * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv78)
    | MenhirState23 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv79 * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position) * Lexing.position) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _, _menhir_s, _, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv80)
    | MenhirState20 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv81 * Lexing.position * _menhir_state * 'tv_int_expr * Lexing.position)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv82)
    | MenhirState18 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv83 * _menhir_state * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv84)
    | MenhirState17 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv85 * _menhir_state * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv86)
    | MenhirState16 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv87 * _menhir_state * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv88)
    | MenhirState13 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv89 * _menhir_state * Lexing.position) * Lexing.position) * Lexing.position * _menhir_state * 'tv_sign_int_literal * Lexing.position)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv90)
    | MenhirState6 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv91 * _menhir_state * Lexing.position) * Lexing.position) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv92)
    | MenhirState2 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv93 * Lexing.position * _menhir_state * (
# 54 "frontend/parser.mly"
       (string)
# 3017 "frontend/parser.ml"
        ) * Lexing.position)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv94)
    | MenhirState0 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv95) = Obj.magic _menhir_stack in
        (raise _eRR : 'freshtv96)

and _menhir_reduce28 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _v : 'tv_list_ext_stat__ = 
# 186 "/home/tas/.opam/system/lib/menhir/standard.mly"
    ( [] )
# 3031 "frontend/parser.ml"
     in
    _menhir_goto_list_ext_stat__ _menhir_env _menhir_stack _menhir_s _v

and _menhir_run1 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> (
# 54 "frontend/parser.mly"
       (string)
# 3038 "frontend/parser.ml"
) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    let _menhir_stack = (_menhir_stack, _endpos, _menhir_s, _v, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | TOK_EQUAL ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv27 * Lexing.position * _menhir_state * (
# 54 "frontend/parser.mly"
       (string)
# 3050 "frontend/parser.ml"
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
# 54 "frontend/parser.mly"
       (string)
# 3078 "frontend/parser.ml"
        ) * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv30)

and _menhir_run33 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
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
            _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState34 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_FALSE ->
            _menhir_run37 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState34 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_LPAREN ->
            _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState34 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_MINUS ->
            _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState34 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_PLUS ->
            _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState34 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_RAND ->
            _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState34 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_TRUE ->
            _menhir_run35 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState34 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_id _v ->
            _menhir_run4 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState34 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_int _v ->
            _menhir_run3 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState34 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState34) : 'freshtv24)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv25 * _menhir_state * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv26)

and _menhir_run62 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
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
            _menhir_run64 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState63 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_RPAREN ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv17) = Obj.magic _menhir_stack in
            let (_menhir_s : _menhir_state) = MenhirState63 in
            ((let _v : 'tv_loption_separated_nonempty_list_TOK_COMMA_ext_TOK_id___ = 
# 129 "/home/tas/.opam/system/lib/menhir/standard.mly"
    ( [] )
# 3150 "frontend/parser.ml"
             in
            _menhir_goto_loption_separated_nonempty_list_TOK_COMMA_ext_TOK_id___ _menhir_env _menhir_stack _menhir_s _v) : 'freshtv18)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState63) : 'freshtv20)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv21 * _menhir_state * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv22)

and _menhir_run71 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | TOK_INT ->
        _menhir_run72 _menhir_env (Obj.magic _menhir_stack) MenhirState71 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_ASSERT | TOK_HALT | TOK_IF | TOK_LCURLY | TOK_PRINT | TOK_RCURLY | TOK_WHILE | TOK_id _ ->
        _menhir_reduce26 _menhir_env (Obj.magic _menhir_stack) MenhirState71
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState71

and _menhir_run77 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
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
            _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState78 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_FALSE ->
            _menhir_run37 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState78 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_LPAREN ->
            _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState78 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_MINUS ->
            _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState78 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_PLUS ->
            _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState78 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_RAND ->
            _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState78 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_TRUE ->
            _menhir_run35 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState78 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_id _v ->
            _menhir_run4 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState78 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_int _v ->
            _menhir_run3 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState78 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState78) : 'freshtv14)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv15 * _menhir_state * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv16)

and _menhir_run81 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
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
# 207 "frontend/parser.mly"
  ( AST_HALT )
# 3246 "frontend/parser.ml"
         in
        _menhir_goto_stat _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv8)) : 'freshtv10)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv11 * _menhir_state * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv12)

and _menhir_run83 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
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
            _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState84 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_FALSE ->
            _menhir_run37 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState84 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_LPAREN ->
            _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState84 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_MINUS ->
            _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState84 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_PLUS ->
            _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState84 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_RAND ->
            _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState84 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_TRUE ->
            _menhir_run35 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState84 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_id _v ->
            _menhir_run4 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState84 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | TOK_int _v ->
            _menhir_run3 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState84 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState84) : 'freshtv4)
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
# 70 "frontend/parser.mly"
      (Abstract_syntax_tree.prog)
# 3316 "frontend/parser.ml"
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
        _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState0 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_HALT ->
        _menhir_run81 _menhir_env (Obj.magic _menhir_stack) MenhirState0 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_IF ->
        _menhir_run77 _menhir_env (Obj.magic _menhir_stack) MenhirState0 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_LCURLY ->
        _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState0 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_PRINT ->
        _menhir_run62 _menhir_env (Obj.magic _menhir_stack) MenhirState0 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_WHILE ->
        _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState0 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_id _v ->
        _menhir_run1 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState0 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | TOK_EOF ->
        _menhir_reduce28 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState0) : 'freshtv2))

# 218 "frontend/parser.mly"
  

# 3359 "frontend/parser.ml"

# 220 "/home/tas/.opam/system/lib/menhir/standard.mly"
  


# 3365 "frontend/parser.ml"
