-- -*- mode: haskell -*-

{
{-# OPTIONS -w #-}

-- |
-- Module      : Language.Ziria.Parser.Parser
-- Copyright   : (c) 2014-2015 Drexel University
-- License     : BSD-style
-- Author      : Geoffrey Mainland <mainland@cs.drexel.edu>
-- Maintainer  : Geoffrey Mainland <mainland@cs.drexel.edu>

module Language.Ziria.Parser.Parser (
    parseProgram
  ) where

import Control.Applicative ((<$>), (<*>))
import Control.Monad (forM_,
                      when,
                      unless,
                      liftM)
import Control.Monad.Exception
import Data.List (foldl1',
                  intersperse)
import Data.Loc
import Data.Maybe (fromMaybe, catMaybes)
import Data.Monoid
import Data.Symbol
import Text.PrettyPrint.Mainland

import Language.Ziria.Parser.Lexer
import Language.Ziria.Parser.Monad
import qualified Language.Ziria.Parser.Tokens as T
import Language.Ziria.Smart
import Language.Ziria.Syntax

import KZC.Name
}

%token
  STRING      { L _ (T.TstringConst _) }
  INT         { L _ (T.TintConst _) }
  FLOAT       { L _ (T.TfloatConst _) }
  ID          { L _ (T.Tidentifier _) }
  STRUCTID    { L _ (T.TstructIdentifier _) }

  "'0"          { L _ T.TzeroBit }
  "'1"          { L _ T.ToneBit }
  'C'           { L _ T.TC }
  'ST'          { L _ T.TST }
  'T'           { L _ T.TT }
  'arr'         { L _ T.Tarr }
  'autoinline'  { L _ T.Tautoinline }
  'bit'         { L _ T.Tbit }
  'bool'        { L _ T.Tbool }
  'comp'        { L _ T.Tcomp }
  'do'          { L _ T.Tdo }
  'double'      { L _ T.Tdouble }
  'else'        { L _ T.Telse }
  'emit'        { L _ T.Temit }
  'emits'       { L _ T.Temits }
  'error'       { L _ T.Terror }
  'external'    { L _ T.Texternal }
  'false'       { L _ T.Tfalse }
  'filter'      { L _ T.Tfilter }
  'for'         { L _ T.Tfor }
  'forceinline' { L _ T.Tforceinline }
  'fun'         { L _ T.Tfun }
  'if'          { L _ T.Tif }
  'in'          { L _ T.Tin }
  'int'         { L _ T.Tint }
  'int8'        { L _ T.Tint8 }
  'int16'       { L _ T.Tint16 }
  'int32'       { L _ T.Tint32 }
  'int64'       { L _ T.Tint64 }
  'length'      { L _ T.Tlength }
  'let'         { L _ T.Tlet }
  'map'         { L _ T.Tmap }
  'not'         { L _ T.Tnot }
  'noinline'    { L _ T.Tnoinline }
  'nounroll'    { L _ T.Tnounroll }
  'print'       { L _ T.Tprint }
  'println'     { L _ T.Tprintln }
  'read'        { L _ T.Tread }
  'repeat'      { L _ T.Trepeat }
  'return'      { L _ T.Treturn }
  'seq'         { L _ T.Tseq }
  'standalone'  { L _ T.Tstandalone }
  'struct'      { L _ T.Tstruct }
  'take'        { L _ T.Ttake }
  'takes'       { L _ T.Ttakes }
  'then'        { L _ T.Tthen }
  'times'       { L _ T.Ttimes }
  'true'        { L _ T.Ttrue }
  'unroll'      { L _ T.Tunroll }
  'until'       { L _ T.Tuntil }
  'var'         { L _ T.Tvar }
  'while'       { L _ T.Twhile }
  'write'       { L _ T.Twrite }

  '+'  { L _ T.Tplus }
  '-'  { L _ T.Tminus }
  '*'  { L _ T.Tstar }
  '/'  { L _ T.Tdiv }
  '%'  { L _ T.Trem }
  '**' { L _ T.Texp }
  '<<' { L _ T.Tshiftl }
  '>>' { L _ T.Tshiftr }

  '=='  { L _ T.Teq }
  '!='  { L _ T.Tne }
  '<'   { L _ T.Tlt }
  '>'   { L _ T.Tgt }
  '<='  { L _ T.Tle }
  '>='  { L _ T.Tge }

  '~' { L _ T.Tbneg }
  '&' { L _ T.Tband }
  '|' { L _ T.Tbor }
  '^' { L _ T.Tbxor }

  '&&' { L _ T.Tland }
  '||' { L _ T.Tlor }

  '='     { L _ T.Tdef }
  ':='    { L _ T.Tassign }
  '<-'    { L _ T.Tbind }
  '>>>'   { L _ T.Tcompose }
  '|>>>|' { L _ T.Tpcompose }

  '('  { L _ T.Tlparen }
  ')'  { L _ T.Trparen }
  '['  { L _ T.Tlbrack }
  ']'  { L _ T.Trbrack }
  '{'  { L _ T.Tlbrace }
  '}'  { L _ T.Trbrace }

  '!'  { L _ T.Tbang }
  '.'  { L _ T.Tdot }
  ','  { L _ T.Tcomma }
  ';'  { L _ T.Tsemi }
  ':'  { L _ T.Tcolon }

-- We give 'if'...'else' a higher precedence than an 'if' without an 'else'
-- clause.
%nonassoc IF
%nonassoc 'else'

-- We give function calls higher precedence than named identifiers. We have to
-- do this because of constructs like 'while' exp acomp and because of the
-- optional semicolon in commands, both of which make things like f (...)
-- ambiguous---there's no way to tell if that if a function call, or if 'f' is a
-- complete expression/computation.
%nonassoc ID
%nonassoc '('

%left ','
%left '&&' '||'
%left '==' '!='
%left '|'
%left '^'
%left '&'
%left '<' '<=' '>' '>='
%left '<<' '>>'
%left '+' '-'
%left '*' '/' '%' '**'
%left 'length'
%left '~' 'not' NEG

%left '|>>>|'
%left '>>>'

%expect 0

%monad { P } { >>= } { return }
%lexer { lexer } { L _ T.Teof }
%tokentype { (L T.Token) }
%error { happyError }

%name parseProgram program

%%
{------------------------------------------------------------------------------
 -
 - Identifiers
 -
 ------------------------------------------------------------------------------}

identifier :: { Var }
identifier :
    ID       { mkVar $ mkSymName (getID $1) (locOf $1) }
  | STRUCTID { mkVar $ mkSymName (getSTRUCTID $1) (locOf $1) }
  | 'arr'    { mkVar $ mkName "arr" (locOf $1) }
  | 'fun'    { mkVar $ mkName "fun" (locOf $1) }
  | 'length' { mkVar $ mkName "length" (locOf $1) }

{------------------------------------------------------------------------------
 -
 - Values
 -
 ------------------------------------------------------------------------------}

scalar_value :: { L Const }
scalar_value :
    '(' ')' { L (locOf $1) UnitC }
  | 'true'  { L (locOf $1) $ BoolC True }
  | 'false' { L (locOf $1) $ BoolC False }
  | "'0"    { L (locOf $1) $ BitC False }
  | "'1"    { L (locOf $1) $ BitC True }
  | INT     { L (locOf $1) $ IntC W32 (snd (getINT $1)) }
  | FLOAT   { L (locOf $1) $ FloatC W32 (snd (getFLOAT $1)) }
  | STRING  { L (locOf $1) $ StringC (snd (getSTRING $1)) }

{------------------------------------------------------------------------------
 -
 - Expressions
 -
 ------------------------------------------------------------------------------}

exp :: { Exp }
exp :
    bexp             { $1 }
  | '{' exp_list '}' { ArrayE $2 ($1 `srcspan` $2) }

const_exp :: { Exp }
const_exp :
    scalar_value
      { ConstE (unLoc $1) (srclocOf $1) }

  | const_exp '+' const_exp
      { BinopE Add $1 $3 ($1 `srcspan` $3)}
  | const_exp '-' const_exp
      { BinopE Sub $1 $3 ($1 `srcspan` $3)}
  | const_exp '*' const_exp
      { BinopE Mul $1 $3 ($1 `srcspan` $3)}
  | const_exp '/' const_exp
      { BinopE Div $1 $3 ($1 `srcspan` $3)}
  | const_exp '%' const_exp
      { BinopE Rem $1 $3 ($1 `srcspan` $3)}
  | const_exp '**' const_exp
      { BinopE Pow $1 $3 ($1 `srcspan` $3)}
  | const_exp '<<' const_exp
      { BinopE LshL $1 $3 ($1 `srcspan` $3)}
  | const_exp '>>' const_exp
      { BinopE AshR $1 $3 ($1 `srcspan` $3)}
  | const_exp '&' const_exp
      { BinopE Band $1 $3 ($1 `srcspan` $3)}
  | const_exp '|' const_exp
      { BinopE Bor $1 $3 ($1 `srcspan` $3)}
  | const_exp '^' const_exp
      { BinopE Bxor $1 $3 ($1 `srcspan` $3)}
  | const_exp '==' const_exp
      { BinopE Eq $1 $3 ($1 `srcspan` $3)}
  | const_exp '!=' const_exp
      { BinopE Ne $1 $3 ($1 `srcspan` $3)}
  | const_exp '<' const_exp
      { BinopE Lt $1 $3 ($1 `srcspan` $3)}
  | const_exp '>' const_exp
      { BinopE Gt $1 $3 ($1 `srcspan` $3)}
  | const_exp '<=' const_exp
      { BinopE Le $1 $3 ($1 `srcspan` $3)}
  | const_exp '>=' const_exp
      { BinopE Ge $1 $3 ($1 `srcspan` $3)}
  | const_exp '&&' const_exp
      { BinopE Land $1 $3 ($1 `srcspan` $3)}
  | const_exp '||' const_exp
      { BinopE Lor $1 $3 ($1 `srcspan` $3)}

  | '-' const_exp %prec NEG
      { UnopE Neg $2 ($1 `srcspan` $2)}
  | 'not' const_exp
      { UnopE Lnot $2 ($1 `srcspan` $2)}
  | '~' const_exp
      { UnopE Bnot $2 ($1 `srcspan` $2)}

  | '(' const_exp ')'
      { $2 }
  | '(' const_exp error
      {% unclosed ($1 <--> $2) "(" }

pexp :: { Exp }
pexp :
    ID
      { varE (mkVar (varid $1)) }
  | pexp '.' ID
      { ProjE $1 (mkField (fieldid $3)) ($1 `srcspan` $3) }
  | pexp '[' exp ':' const_int_exp ']'
      {% do { from      <- constIntExp $3
            ; let to    =  unLoc $5
            ; let len   =  to - from
            ; let efrom =  ConstE (IntC W32 from) (srclocOf $5)
            ; return $ IdxE $1 efrom (Just (fromInteger len)) ($1 `srcspan` $6)
            }
      }
  | pexp '[' exp ',' const_int_exp ']'
      { IdxE $1 $3 (Just (fromInteger (unLoc $5))) ($1 `srcspan` $6) }
  | pexp '[' exp ']'
      { IdxE $1 $3 Nothing ($1 `srcspan` $4) }

aexp :: { Exp }
aexp :
    pexp
      { $1 }
  | scalar_value
      { ConstE (unLoc $1) (srclocOf $1) }
  | 'arr' '{' exp_list '}'
      { ArrayE $3 ($1 `srcspan` $4) }

  | aexp '+' aexp
      { BinopE Add $1 $3 ($1 `srcspan` $3)}
  | aexp '-' aexp
      { BinopE Sub $1 $3 ($1 `srcspan` $3)}
  | aexp '*' aexp
      { BinopE Mul $1 $3 ($1 `srcspan` $3)}
  | aexp '/' aexp
      { BinopE Div $1 $3 ($1 `srcspan` $3)}
  | aexp '%' aexp
      { BinopE Rem $1 $3 ($1 `srcspan` $3)}
  | aexp '**' aexp
      { BinopE Pow $1 $3 ($1 `srcspan` $3)}
  | aexp '<<' aexp
      { BinopE LshL $1 $3 ($1 `srcspan` $3)}
  | aexp '>>' aexp
      { BinopE AshR $1 $3 ($1 `srcspan` $3)}
  | aexp '&' aexp
      { BinopE Band $1 $3 ($1 `srcspan` $3)}
  | aexp '|' aexp
      { BinopE Bor $1 $3 ($1 `srcspan` $3)}
  | aexp '^' aexp
      { BinopE Bxor $1 $3 ($1 `srcspan` $3)}
  | aexp '==' aexp
      { BinopE Eq $1 $3 ($1 `srcspan` $3)}
  | aexp '!=' aexp
      { BinopE Ne $1 $3 ($1 `srcspan` $3)}
  | aexp '<' aexp
      { BinopE Lt $1 $3 ($1 `srcspan` $3)}
  | aexp '>' aexp
      { BinopE Gt $1 $3 ($1 `srcspan` $3)}
  | aexp '<=' aexp
      { BinopE Le $1 $3 ($1 `srcspan` $3)}
  | aexp '>=' aexp
      { BinopE Ge $1 $3 ($1 `srcspan` $3)}
  | aexp '&&' aexp
      { BinopE Land $1 $3 ($1 `srcspan` $3)}
  | aexp '||' aexp
      { BinopE Lor $1 $3 ($1 `srcspan` $3)}

  | '-' aexp %prec NEG
      { UnopE Neg $2 ($1 `srcspan` $2)}
  | 'not' aexp
      { UnopE Lnot $2 ($1 `srcspan` $2)}
  | '~' aexp
      { UnopE Bnot $2 ($1 `srcspan` $2)}

  | 'length' aexp
      { UnopE Len $2 ($1 `srcspan` $2)}
  | cast_type '(' exp ')'
      { UnopE (Cast $1) $3 ($1 `srcspan` $4)}

  | structid '{' struct_init_list1 '}'
      { StructE $1 $3 ($1 `srcspan` $4) }

  | ID '(' exp_list ')'
      { CallE (mkVar (varid $1)) $3 ($1 `srcspan` $4) }

  | '(' exp ')'
      { $2 }
  | '(' exp error
      {% unclosed ($1 <--> $2) "(" }

bexp :: { Exp }
bexp :
    aexp
      { $1 }

  | 'if' bexp 'then' bexp 'else' bexp
      { IfE $2 $4 (Just $6) ($1 `srcspan` $6) }
  | 'if' bexp 'then' bexp 'else' error
      {% expected ["expression"] Nothing }
  | 'if' bexp 'then' bexp error
      {% expected ["else clause"] Nothing }
  | 'if' bexp 'then' error
      {% expected ["expression"] Nothing }
  | 'if' bexp error
      {% expected ["then clause"] Nothing }

  | 'let' var_bind '=' exp 'in' bexp_or_stms
      { let { (v, tau) = $2 }
        in
          LetE v tau $4 $6 ($1 `srcspan` $6)
      }
  | 'var' ID ':' base_type maybe_initializer 'in' bexp_or_stms
      { LetRefE (mkVar (varid $2)) $4 $5 $7 ($1 `srcspan` $7) }

bexp_or_stms :: { Exp }
bexp_or_stms :
    bexp         { $1 }
  | '{' stms '}' { StmE $2 ($1 `srcspan` $3) }

-- Variable binding
var_bind :: { (Var, Maybe Type) }
var_bind :
    identifier
      { ($1, Nothing) }
  | '(' identifier ':' base_type ')'
      { ($2, Just $4) }

-- Mutable variable initializer
maybe_initializer :: { Maybe Exp }
maybe_initializer :
    {- empty -} { Nothing }
  | ':=' exp    { Just $2 }

-- Constant integer expressions
const_int_exp :: { L Integer }
const_int_exp :
    const_exp {% fmap (L (locOf $1)) (constIntExp $1) }

-- List of zero or more expressions
exp_list :: { [Exp] }
exp_list :
    exp_rlist { rev $1 }

exp_rlist :: { RevList Exp }
exp_rlist :
    {- empty -}       { rnil }
  | exp               { rsingleton $1 }
  | exp_rlist ',' exp { rcons $3 $1 }

-- List of one or more expressions
exp_list1 :: { [Exp] }
exp_list1 :
    exp_rlist1 { rev $1 }

exp_rlist1 :: { RevList Exp }
exp_rlist1 :
    exp                { rsingleton $1 }
  | exp_rlist1 ',' exp { rcons $3 $1 }

-- Struct initializers
structid :: { Struct }
structid :
    STRUCTID { mkStruct $ mkSymName (getSTRUCTID $1) (locOf $1) }

struct_init_list1 :: { [(Field, Exp)] }
struct_init_list1 :
    struct_init1_rlist { rev $1 }

struct_init1_rlist :: { RevList (Field, Exp) }
struct_init1_rlist :
    struct_init                        { rsingleton $1 }
  | struct_init1_rlist ';' struct_init { rcons $3 $1 }

struct_init :: { (Field, Exp) }
struct_init :
    ID '=' exp { (mkField (fieldid $1), $3) }

gen_interval :: { L (Exp, Exp) }
gen_interval :
    '[' exp ':' const_int_exp ']'
      {% do { from     <- constIntExp $2
            ; let to   =  unLoc $4
            ; let len  =  to - from
            ; return $L ($1 <--> $5) (ConstE (IntC W32 from) (srclocOf $2), ConstE (IntC W32 len) (srclocOf $4))
            }
      }
  | '[' exp ',' exp ']'
      {L ($1 <--> $5) ($2, $4) }

{------------------------------------------------------------------------------
 -
 - Types
 -
 ------------------------------------------------------------------------------}

base_type :: { Type }
base_type :
    '(' ')'           { UnitT ($1 `srcspan` $2) }
  | 'bool'            { BoolT (srclocOf $1) }
  | 'bit'             { BitT (srclocOf $1) }
  | 'int'             { IntT W32 (srclocOf $1) }
  | 'int8'            { IntT W8 (srclocOf $1) }
  | 'int16'           { IntT W16 (srclocOf $1) }
  | 'int32'           { IntT W32 (srclocOf $1) }
  | 'int64'           { IntT W64 (srclocOf $1) }
  | 'double'          { FloatT W64 (srclocOf $1) }
  | 'arr' arr_length  { let { (ind, tau) = $2 }
                        in
                          ArrT ind tau ($1 `srcspan` tau)
                      }
  | structid          { StructT $1 (srclocOf $1) }
  | 'struct' structid { StructT $2 ($1 `srcspan` $2) }
  | '(' base_type ')' { $2 }

cast_type :: { Type }
cast_type :
    'bit'    { BitT (srclocOf $1) }
  | 'int'    { IntT W32 (srclocOf $1) }
  | 'int8'   { IntT W8 (srclocOf $1) }
  | 'int16'  { IntT W16 (srclocOf $1) }
  | 'int32'  { IntT W32 (srclocOf $1) }
  | 'int64'  { IntT W64 (srclocOf $1) }
  | 'double' { FloatT W64 (srclocOf $1) }
  | structid { StructT $1 (srclocOf $1) }

arr_length :: { (Ind, Type) }
arr_length :
    '[' 'length' '(' ID ')' ']' base_type
      { (ArrI (mkVar (varid $4)) ($2 `srcspan` $5), $7) }
  | '[' const_int_exp ']' base_type
      { (ConstI (fromInteger (unLoc $2)) (srclocOf $2), $4) }
  | base_type
      { (NoneI (srclocOf $1), $1) }

comp_base_type :: { Type }
comp_base_type :
    'ST' index_type base_type base_type
      { ST $2 $3 $4 ($1 `srcspan` $4) }
  | '(' comp_base_type ')'
      { $2 }

index_type :: { Type }
index_type :
    'T'                { T (srclocOf $1) }
  | 'C' base_type      { C $2 ($1 `srcspan` $2) }
  | '(' index_type ')' { $2 }

{------------------------------------------------------------------------------
 -
 - Statements
 -
 ------------------------------------------------------------------------------}

stm_block :: { [Stm] }
stm_block :
    '{' stms '}' { $2 }
  | stm_exp      { [ExpS $1 (srclocOf $1)] }

stms :: { [Stm] }
stms :
    stm_rlist opt_semi { rev $1 }

stm_rlist :: { RevList Stm }
stm_rlist :
    stm                    { rsingleton $1 }
  | stm_rlist opt_semi stm { rcons $3 $1 }

stm :: { Stm }
stm :
    'let' var_bind '=' exp
      { let { (v, tau) = $2 }
        in
          LetS v tau $4 ($1 `srcspan` $4)
      }
  | 'var' ID ':' base_type maybe_initializer
      { LetRefS (mkVar (varid $2)) $4 $5 ($1 `srcspan` $5) }
  | stm_exp { ExpS $1 (srclocOf $1) }

stm_exp :: { Exp }
stm_exp :
    unroll_info 'for' var_bind 'in' gen_interval stm_block
      { let { uann        = unLoc $1
            ; (v, tau)    = $3
            ; (from, len) = unLoc $5
            ; body        = $6
            }
        in
          ForE uann v tau from len (stmsE body) ($1 `srcspan` $6)
      }
  | 'while' '(' exp ')' stm_block
      { WhileE $3 (stmsE $5) ($1 `srcspan` $5) }

  | 'return' exp
      { ReturnE AutoInline $2 ($1 `srcspan` $2) }

  | 'print' exp_list1
      { PrintE False $2 ($1 `srcspan` $2) }
  | 'println' exp_list1
      { PrintE True $2 ($1 `srcspan` $2) }
  | 'error' STRING
      { ErrorE (snd (getSTRING $2)) ($1 `srcspan` $2) }

  | ID '(' exp_list ')'
      { CallE (mkVar (varid $1)) $3 ($1 `srcspan` $4) }
  | STRUCTID '(' exp_list ')'
      { CallE (mkVar (structid $1)) $3 ($1 `srcspan` $4) }

  | pexp ':=' exp
      { AssignE $1 $3 ($1 `srcspan` $3) }

  | 'if' exp 'then' stm_block 'else' stm_block
      { IfE $2 (stmsE $4) (Just (stmsE $6)) ($1 `srcspan` $6) }
  | 'if' exp 'then' stm_block 'else' error
      {% expected ["statement block"] Nothing }
  | 'if' exp 'then' stm_block %prec IF
      { let { loc = ($1 `srcspan` $4) }
        in
          IfE $2 (stmsE $4) Nothing loc
      }
  | 'if' exp error
      {% expected ["then clause"] Nothing }

  | 'let' var_bind '=' exp 'in' stm_block
      { let { (v, tau) = $2 }
        in
          LetE v tau $4 (stmsE $6) ($1 `srcspan` $6)
      }
  | 'var' ID ':' base_type maybe_initializer 'in' stm_block
      { LetRefE (mkVar (varid $2)) $4 $5 (stmsE $7) ($1 `srcspan` $7) }

unroll_info :: { L UnrollAnn }
unroll_info :
    {- empty -} { L NoLoc      AutoUnroll }
  | 'unroll'    { L (locOf $1) Unroll }
  | 'nounroll'  { L (locOf $1) NoUnroll }

{------------------------------------------------------------------------------
 -
 - Computation Expressions
 -
 ------------------------------------------------------------------------------}

commands :: { [Cmd] }
commands :
    {- empty -}
      { [] }
  | comp_let_decl opt_semi commands
      { LetC $1 (srclocOf $1) : $3 }
  | var_bind '<-' comp opt_semi commands
      { let { (v, tau) = $1
            ; body     = $3
            }
        in
          BindC v tau body (v `srcspan` $3) : $5
      }
  | comp opt_semi commands
      { ExpC $1 (srclocOf $1) : $3 }

comp_let_decl :: { CompLet }
comp_let_decl :
    'let' var_bind '=' exp
      { let { (v, tau) = $2 }
        in
          LetCL v tau $4 ($1 `srcspan` $4)
      }
  | 'let' var_bind error
      {% expected ["'='"] Nothing }
  | 'var' ID ':' base_type maybe_initializer
      { LetRefCL (mkVar (varid $2)) $4 $5 ($1 `srcspan` $5) }
  | struct
      { LetStructCL $1 (srclocOf $1) }
  | 'fun' 'external' ID params ':' base_type
      { LetFunExternalCL (mkVar (varid $3)) $4 $6 ($1 `srcspan` $6) }
  | 'fun' 'comp' maybe_comp_range comp_var_bind comp_params '{' commands '}'
      { let { (v, tau) = $4 }
        in
          LetFunCompCL v tau $3 $5 (cmdsE $7) ($1 `srcspan` $8)
      }
  | 'fun' var_bind params stm_block
      { let { (v, tau) = $2 }
        in
          LetFunCL v tau $3 (stmsE $4) ($1 `srcspan` $4)
      }
  | 'let' 'comp' maybe_comp_range comp_var_bind '=' comp
      { let { (v, tau) = $4 }
        in
          LetCompCL v tau $3 $6 ($1 `srcspan` $6)
      }

acomp :: { Exp }
acomp :
    'standalone' acomp
      { StandaloneE $2 ($1 `srcspan` $2) }
  | 'repeat' vect_ann acomp
      { RepeatE $2 $3 ($1 `srcspan` $3) }
  | 'until' exp acomp
      { UntilE $2 $3 ($1 `srcspan` $3) }
  | 'while' exp acomp
      { WhileE $2 $3 ($1 `srcspan` $3) }
  | unroll_info 'times' exp acomp
      { TimesE (unLoc $1) $3 $4 ($1 `srcspan` $4) }
  | unroll_info 'for' var_bind 'in' gen_interval acomp
      { let { (v, tau)     = $3
            ; (start, len) = unLoc $5
            }
        in
          ForE (unLoc $1) v tau start len $6 ($1 `srcspan` $6)
      }
  | inline_ann 'return' exp
      { ReturnE (unLoc $1) $3 ($1 `srcspan` $3) }
  | 'emit' exp
      { EmitE $2 ($1 `srcspan` $2) }
  | 'emits' exp
      { EmitsE $2 ($1 `srcspan` $2) }
  | 'take'
      { TakeE (srclocOf $1) }
  | 'takes' const_int_exp
      { TakesE (fromInteger (unLoc $2)) ($1 `srcspan` $2) }
  | 'filter' var_bind
      { let { (v, tau) = $2 }
        in
          FilterE v tau ($1 `srcspan` tau)
      }
  | 'read' type_ann
      { ReadE (unLoc $2) ($1 `srcspan` $2) }
  | 'write' type_ann
      { WriteE (unLoc $2) ($1 `srcspan` $2) }
  | 'map' vect_ann var_bind
      { let { (v, tau) = $3 }
        in
          MapE $2 v tau ($1 `srcspan` tau)
      }

  | 'do' stm_block
      { stmsE $2 }
  | 'seq' '{' commands '}'
      { cmdsE $3 }
  | '{' commands '}'
      { cmdsE $2 }

  | ID
      { varE (mkVar (varid $1)) }
  | ID '(' exp_list ')'
      { CallE (mkVar (varid $1)) $3 ($1 `srcspan` $4) }
  | STRUCTID '(' exp_list ')'
      { CallE (mkVar (structid $1)) $3 ($1 `srcspan` $4) }

  | '(' comp ')'
      { $2 }

opcomp :: { Exp }
opcomp :
    acomp
      { $1 }
  | opcomp '>>>' opcomp
      { ArrE AutoPipeline $1 $3 ($1 `srcspan` $3) }
  | opcomp '|>>>|' opcomp
      { ArrE Pipeline $1 $3 ($1 `srcspan` $3) }

ifcomp :: { Exp }
ifcomp :
    opcomp
      { $1 }
  | 'if' exp 'then' ifcomp %prec IF
      { IfE $2 $4 Nothing ($1 `srcspan` $4) }
  | 'if' exp 'then' ifcomp 'else' ifcomp
      { IfE $2 $4 (Just $6) ($1 `srcspan` $6) }
  | 'if' exp 'then' error
      {% expected ["command"] Nothing }
  | 'if' exp error
      {% expected ["then clause"] Nothing }

comp :: { Exp }
comp :
    ifcomp
      { $1 }
  | comp_let_decl 'in' comp
      { CompLetE $1 $3 ($1 `srcspan` $3) }
  | comp_let_decl error
      {% expected ["'in'"] Nothing }

inline_ann :: { L InlineAnn }
inline_ann :
    {- empty -}   { L NoLoc      AutoInline }
  | 'noinline'    { L (locOf $1) NoInline }
  | 'forceinline' { L (locOf $1) Inline }
  | 'autoinline'  { L (locOf $1) AutoInline }

type_ann :: { L (Maybe Type) }
type_ann :
    {- empty -}       { L NoLoc        Nothing }
  | '[' base_type ']' { L ($1 <--> $3) (Just $2) }

vect_ann :: { VectAnn }
vect_ann :
    {- empty -}
      { AutoVect }
  | vect_ann_flag
      { let { (flag, (from, to)) = $1 }
        in
          Rigid flag from to
      }
  | '<=' vect_ann_flag
      { let { (flag, (from, to)) = $2 }
        in
          UpTo flag from to
      }

vect_ann_flag :: { (Bool, (Int, Int)) }
vect_ann_flag :
    comp_range     { (True,  $1) }
  | '!' comp_range { (False, $2) }

-- Comp ranges
comp_range :: { (Int, Int) }
comp_range :
    '[' INT ',' INT ']' { (fromIntegral (snd (getINT $2)), fromIntegral (snd (getINT $4))) }

maybe_comp_range :: { Maybe (Int, Int) }
maybe_comp_range :
    {- empty -} { Nothing }
  | comp_range  { Just $1 }

-- Comp variable binding
comp_var_bind :: { (Var, Maybe Type) }
comp_var_bind :
    identifier
      {% do { -- addCompIdentifier (symbol $1)
            ; return ($1, Nothing)
            }
      }
  | '(' identifier ':' comp_base_type ')'
      {% do { -- addCompIdentifier (symbol $2)
            ; return ($2, Just $4)
            }
      }

-- structs
struct :: { StructDef }
struct :
    'struct' ID '=' '{' field_list '}'
      {% do { addStructIdentifier (getID $2)
            ; return $ StructDef (mkStruct (varid $2)) $5 ($1 `srcspan` $6)
            }
      }

field_list :: { [(Field, Type)] }
field_list :
    field_rlist { rev $1 }

field_rlist :: { RevList (Field, Type) }
field_rlist :
    {- empty -}           { rnil }
  | field                 { rsingleton $1 }
  | field_rlist ';' field { rcons $3 $1 }

field :: { (Field, Type) }
field :
    ID ':' base_type { (mkField (fieldid $1), $3) }

-- Parameters to a (non-comp) function
params :: { [VarBind] }
params :
    '(' param_rlist ')' { rev $2 }

param_rlist :: { RevList VarBind }
param_rlist :
    {- empty -}           { rnil }
  | param                 { rsingleton $1 }
  | param_rlist ',' param { rcons $3 $1 }

param :: { VarBind  }
param :
    'var' ID ':' base_type
      { VarBind (mkVar (varid $2)) True $4 }
  | identifier ':' base_type
      { VarBind $1 False $3 }

-- Parameters to a comp function
comp_params :: { [VarBind] }
comp_params :
    '(' comp_param_rlist ')' { rev $2 }

comp_param_rlist :: { RevList VarBind }
comp_param_rlist :
    {- empty -}                     { rnil }
  | comp_param                      { rsingleton $1 }
  | comp_param_rlist ',' comp_param { rcons $3 $1 }

comp_param :: { VarBind }
comp_param :
    'var' ID ':' base_type
      { VarBind (mkVar (varid $2)) True $4 }
  | 'var' ID ':' comp_base_type
      {% fail "Computation parameter cannot be mutable" }
  | ID ':' base_type
      { VarBind (mkVar (varid $1)) False $3 }
  | ID ':' comp_base_type
      { VarBind (mkVar (varid $1)) False $3 }
  | ID ':' error
      {% expected ["'ST' or base type"] Nothing }

{------------------------------------------------------------------------------
 -
 - Programs
 -
 ------------------------------------------------------------------------------}

program :: { [CompLet] }
program :
    comp_let_decl_rlist opt_semi { rev $1 }

comp_let_decl_rlist :: { RevList CompLet }
comp_let_decl_rlist :
    comp_let_decl                              { rsingleton $1 }
  | comp_let_decl_rlist opt_semi comp_let_decl { rcons $3 $1 }

{------------------------------------------------------------------------------
 -
 - Miscellaneous
 -
 ------------------------------------------------------------------------------}

opt_semi :: { () }
opt_semi :
    {- empty -} { () }
  | ';'         { () }

{
happyError :: L T.Token -> P a
happyError (L loc t) =
    parserError (locStart loc) (text "parse error on" <+> quote (ppr t))
  where
    quote :: Doc -> Doc
    quote = enclose (char '`') (char '\'')

getINT         (L _ (T.TintConst x))             = x
getFLOAT       (L _ (T.TfloatConst x))           = x
getCHAR        (L _ (T.TcharConst x))            = x
getSTRING      (L _ (T.TstringConst x))          = x
getID          (L _ (T.Tidentifier ident))       = ident
getSTRUCTID    (L _ (T.TstructIdentifier ident)) = ident

lexer :: (L T.Token -> P a) -> P a
lexer cont = do
    t <- lexToken
    setCurToken t
    cont t

locate :: Loc -> (SrcLoc -> a) -> L a
locate loc f = L loc (f (SrcLoc loc))

varid :: L T.Token -> Name
varid t = mkSymName (getID t) (locOf t)

structid :: L T.Token -> Name
structid t = mkSymName (getSTRUCTID t) (locOf t)

fieldid :: L T.Token -> Name
fieldid t = mkSymName (getID t) (locOf t)

constIntExp :: Exp -> P Integer
constIntExp e = go e
  where
    go :: Exp -> P Integer
    go (ConstE (IntC _ i) _) = return i
    go (BinopE op e1 e2 _) = do
        x <- go e1
        y <- go e2
        binop op x y

    go _ =
        fail $ "non-constant integer expression: " ++ show e

    binop :: Binop -> Integer -> Integer -> P Integer
    binop Add x y = return $ x + y
    binop Sub x y = return $ x - y
    binop Mul x y = return $ x * y
    binop Div x y = return $ x `div` y
    binop _ _ _   = fail $ "non-constant integer expression: " ++ show e

data RevList a  =  RNil
                |  RCons a (RevList a)
                |  RApp [a] (RevList a)

rnil :: RevList a
rnil = RNil

rsingleton :: a -> RevList a
rsingleton x = RCons x RNil

infixr 5 `rcons`

rcons :: a -> RevList a -> RevList a
rcons x xs  = RCons x xs

rapp :: [a] -> RevList a -> RevList a
rapp xs ys  = RApp xs ys

rlist :: [a] -> RevList a
rlist xs = rlist' xs rnil
  where
    rlist' []     acc = acc
    rlist' (x:xs) acc = rlist' xs (rcons x acc)

rev :: RevList a -> [a]
rev xs = go [] xs
  where
    go  l  RNil          = l
    go  l  (RCons x xs)  = go (x : l) xs
    go  l  (RApp xs ys)  = go (xs ++ l) ys

instance Located a => Located (RevList a) where
    locOf RNil         = mempty
    locOf (RCons x xs) = locOf x `mappend` locOf xs
    locOf (RApp xs ys) = locOf xs `mappend` locOf ys
}
