-- -*- mode: haskell -*-

{
{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS -w #-}

-- |
-- Module      : Language.Ziria.Parser.Kyllini
-- Copyright   : (c) 2014-2017 Drexel University
-- License     : BSD-style
-- Author      : Geoffrey Mainland <mainland@drexel.edu>
-- Maintainer  : Geoffrey Mainland <mainland@drexel.edu>

module Language.Ziria.Parser.Kyllini (
    parseProgram,
    parseImports
  ) where

import Control.Applicative ((<$>), (<*>))
import Control.Monad.Exception
#if !MIN_VERSION_base(4,13,0)
import Control.Monad.Fail (MonadFail)
#endif /* !MIN_VERSION_base(4,13,0) */
import Data.List (foldl1',
                  intersperse)
import Data.Loc
import Data.Maybe (fromMaybe, catMaybes)
import Data.Monoid
import Data.Ratio
import Data.Symbol
import Text.PrettyPrint.Mainland
import Text.PrettyPrint.Mainland.Class

import Language.Ziria.Parser.Lexer
import Language.Ziria.Parser.Monad
import qualified Language.Ziria.Parser.Tokens as T
import Language.Ziria.Parser.Util
import Language.Ziria.Smart
import Language.Ziria.Syntax

import KZC.Name
import KZC.Util.Pretty
}

%token
  STRING      { L _ (T.TstringConst _) }
  INT         { L _ (T.TintConst T.S (_, _)) }
  UINT        { L _ (T.TintConst T.U (_, _)) }
  FLOAT       { L _ (T.TfloatConst _) }
  ID          { L _ (T.Tidentifier _) }
  STRUCTID    { L _ (T.TstructIdentifier _) }

  INT_TYPE   { L _ (T.Ti _) }
  UINT_TYPE  { L _ (T.Tu _) }
  FLOAT_TYPE { L _ (T.Tf _) }
  Q_TYPE     { L _ (T.Tq _ _) }
  UQ_TYPE    { L _ (T.Tq _ _) }

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
  'double'      { L _ T.Tdouble }
  'else'        { L _ T.Telse }
  'emit'        { L _ T.Temit }
  'emits'       { L _ T.Temits }
  'error'       { L _ T.Terror }
  'external'    { L _ T.Texternal }
  'false'       { L _ T.Tfalse }
  'filter'      { L _ T.Tfilter }
  'float'       { L _ T.Tfloat }
  'for'         { L _ T.Tfor }
  'forceinline' { L _ T.Tforceinline }
  'fun'         { L _ T.Tfun }
  'if'          { L _ T.Tif }
  'import'      { L _ T.Timport }
  'impure'      { L _ T.Timpure }
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
  'repeat'      { L _ T.Trepeat }
  'return'      { L _ T.Treturn }
  'standalone'  { L _ T.Tstandalone }
  'struct'      { L _ T.Tstruct }
  'take'        { L _ T.Ttake }
  'takes'       { L _ T.Ttakes }
  'then'        { L _ T.Tthen }
  'times'       { L _ T.Ttimes }
  'true'        { L _ T.Ttrue }
  'uint'        { L _ T.Tuint }
  'uint8'       { L _ T.Tuint8 }
  'uint16'      { L _ T.Tuint16 }
  'uint32'      { L _ T.Tuint32 }
  'uint64'      { L _ T.Tuint64 }
  'unroll'      { L _ T.Tunroll }
  'until'       { L _ T.Tuntil }
  'while'       { L _ T.Twhile }

  '+'  { L _ T.Tplus }
  '-'  { L _ T.Tminus }
  '*'  { L _ T.Tstar }
  '/'  { L _ T.Tdiv }
  '%'  { L _ T.Trem }
  '**' { L _ T.Tpow }
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

  -- For the kyllini dialect
  'bitcast' { L _ T.Tbitcast }
  'cast'    { L _ T.Tcast }
  'mut'     { L _ T.Tmut }
  'nat'     { L _ T.Tnat }
  'type'    { L _ T.Ttype }

  'Eq'         { L _ T.TEq }
  'Ord'        { L _ T.TOrd }
  'Bool'       { L _ T.TBool }
  'Num'        { L _ T.TNum }
  'Integral'   { L _ T.TIntegral }
  'Fractional' { L _ T.TFractional }
  'Bits'       { L _ T.TBits }

  '->' { L _ T.Tarrow }
  '..' { L _ T.Tdotdot }

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
%left '*' '/' '%'
%left '**'
%left 'length'
%left '~' 'not' NEG

%left '|>>>|'
%left '>>>'

%left 'in'

%left STANDALONE

%expect 0

%monad { P } { >>= } { return }
%lexer { lexer } { L _ T.Teof }
%tokentype { (L T.Token) }
%error { happyError }

%name parseProgram program
%partial parseImports imports

%%
{------------------------------------------------------------------------------
 -
 - modules
 -
 ------------------------------------------------------------------------------}

module :: { ModuleName }
module : modids { mkModuleName (map unLoc (rev $1)) (locOf (rev $1)) }

modids :: { RevList (L Symbol) }
modids :
    modid            { rsingleton $1 }
  | modids '.' modid { rcons $3 $1 }

modid :: { L Symbol }
modid :
    ID       { L (locOf $1) (getID $1) }
  | STRUCTID { L (locOf $1) (getSTRUCTID $1) }

{------------------------------------------------------------------------------
 -
 - Identifiers
 -
 ------------------------------------------------------------------------------}

identifier :: { Var }
identifier :
    ID         { mkVar $ mkSymName (getID $1) (locOf $1) }
  | STRUCTID   { mkVar $ mkSymName (getSTRUCTID $1) (locOf $1) }
  | 'arr'      { mkVar $ mkName "arr" (locOf $1) }
  | 'bitcast'  { mkVar $ mkName "bitcast" (locOf $1) }
  | 'cast'     { mkVar $ mkName "cast" (locOf $1) }
  | 'fun'      { mkVar $ mkName "fun" (locOf $1) }
  | 'impure'   { mkVar $ mkName "impure" (locOf $1) }
  | 'length'   { mkVar $ mkName "length" (locOf $1) }
  | INT_TYPE   { mkVar $ mkTypeName "i" (getINT_TYPE $1) (locOf $1) }
  | UINT_TYPE  { mkVar $ mkTypeName "u" (getUINT_TYPE $1) (locOf $1) }
  | FLOAT_TYPE { mkVar $ mkTypeName "f" (getFLOAT_TYPE $1) (locOf $1) }
  | Q_TYPE     { mkVar $ mkType2Name "q" (getQ_TYPE $1) (locOf $1) }
  | UQ_TYPE    { mkVar $ mkType2Name "uq" (getUQ_TYPE $1) (locOf $1) }

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
  | "'0"    { L (locOf $1) $ IntC (U 1) 0 }
  | "'1"    { L (locOf $1) $ IntC (U 1) 1 }
  | INT     { L (locOf $1) $ IntC IDefault (fromIntegral (snd (getINT $1))) }
  | UINT    { L (locOf $1) $ IntC UDefault (fromIntegral (snd (getUINT $1))) }
  | FLOAT   { L (locOf $1) $ FloatC FP64 (snd (getFLOAT $1)) }
  | STRING  { L (locOf $1) $ StringC (snd (getSTRING $1)) }

{------------------------------------------------------------------------------
 -
 - Expressions
 -
 ------------------------------------------------------------------------------}

pexp :: { Exp }
pexp :
    ID
      { varE (mkVar (varid $1)) }
  | pexp '.' ID
      { ProjE $1 (mkField (fieldid $3)) ($1 `srcspan` $3) }
  | pexp '[' exp ']'
      { IdxE $1 $3 Nothing ($1 `srcspan` $4) }
  | pexp '[' exp ':' exp ']'
      {% do { from    <- natExp $3
            ; to      <- natExp $5
            ; let len =  to - from + 1
            ; return $ IdxE $1 $3 (Just len) ($1 `srcspan` $6)
            }
      }

aexp :: { Exp }
aexp :
    scalar_value
      { ConstE (unLoc $1) (srclocOf $1) }
  | '[' exp_list ']'
      { ArrayE $2 ($1 `srcspan` $3) }
  | pexp
      { $1 }

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
  | simple_type '(' exp ')'
      { CastE $1 $3 ($1 `srcspan` $4)}

  | 'bitcast' '<' base_type '>' '(' exp ')'
      { BitcastE $3 $6 ($1 `srcspan` $7)}
  | 'cast' '<' base_type '>' '(' exp ')'
      { CastE $3 $6 ($1 `srcspan` $7)}

  | structid type_application '{' struct_init_list1 '}'
      { StructE $1 $2 $4 ($1 `srcspan` $5) }
  | 'struct' structid type_application '{' struct_init_list1 '}'
      { StructE $2 $3 $5 ($1 `srcspan` $6) }

  | ID '(' exp_list ')'
      { mkCall (varid $1) Nothing $3 ($1 `srcspan` $4) }
  | ID '<' base_type_rlist '>' '(' exp_list ')'
      { mkCall (varid $1) (Just (rev $3)) $6 ($1 `srcspan` $7) }

  | '(' exp ')'
      { $2 }
  | '(' exp error
      {% unclosed ($1 <--> $2) "(" }

exp :: { Exp }
exp :
    aexp
      { $1 }

  | 'if' exp 'then' exp 'else' exp
      { IfE $2 $4 (Just $6) ($1 `srcspan` $6) }
  | 'if' exp 'then' exp 'else' error
      {% expected ["expression"] Nothing }
  | 'if' exp 'then' exp error
      {% expected ["else clause"] Nothing }
  | 'if' exp 'then' error
      {% expected ["expression"] Nothing }
  | 'if' exp error
      {% expected ["then clause"] Nothing }
  | 'if' error
      {% expected ["expression"] Nothing }

  | 'let' var_bind '=' exp 'in' exp_or_stms
      { let { (v, tau) = $2 }
        in
          LetE v tau $4 $6 ($1 `srcspan` $6)
      }
  | 'let' 'mut' var_bind maybe_initializer 'in' exp_or_stms
      { let { (v, tau) = $3 }
        in
          LetRefE v tau $4 $6 ($1 `srcspan` $6)
      }

exp_or_stms :: { Exp }
exp_or_stms :
    exp         { $1 }
  | '{' stms '}' { StmE $2 ($1 `srcspan` $3) }

-- Variable binding
var_bind :: { (Var, Maybe Type) }
var_bind :
    identifier
      { ($1, Nothing) }
  | identifier ':' base_type
      { ($1, Just $3) }

-- Mutable variable initializer
maybe_initializer :: { Maybe Exp }
maybe_initializer :
    {- empty -} { Nothing }
  | '=' exp     { Just $2 }

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
  | struct_init1_rlist ',' struct_init { rcons $3 $1 }

struct_init :: { (Field, Exp) }
struct_init :
    ID '=' exp { (mkField (fieldid $1), $3) }

gen_interval :: { GenInterval }
gen_interval :
    exp '..' exp
      { FromToExclusive $1 $3 ($1 `srcspan` $3) }

{------------------------------------------------------------------------------
 -
 - Types
 -
 ------------------------------------------------------------------------------}

tyvar :: { TyVar }
tyvar :
    ID  { mkTyVar $ mkSymName (getID $1) (locOf $1) }
  | 'T' { mkTyVar $ mkSymName "T" (locOf $1) }
  | 'C' { mkTyVar $ mkSymName "C" (locOf $1) }

simple_type :: { Type }
simple_type :
    'bit'                              { IntT (U 1)    (srclocOf $1) }
  | 'int'                              { IntT IDefault (srclocOf $1) }
  | 'int8'                             { IntT (I 8)    (srclocOf $1) }
  | 'int16'                            { IntT (I 16)   (srclocOf $1) }
  | 'int32'                            { IntT (I 32)   (srclocOf $1) }
  | 'int64'                            { IntT (I 64)   (srclocOf $1) }
  | 'uint'                             { IntT UDefault (srclocOf $1) }
  | 'uint8'                            { IntT (U 8)    (srclocOf $1) }
  | 'uint16'                           { IntT (U 16)   (srclocOf $1) }
  | 'uint32'                           { IntT (U 32)   (srclocOf $1) }
  | 'uint64'                           { IntT (U 64)   (srclocOf $1) }
  | INT_TYPE                           { IntT (I (getINT_TYPE $1)) (srclocOf $1) }
  | UINT_TYPE                          { IntT (U (getUINT_TYPE $1)) (srclocOf $1) }
  | FLOAT_TYPE                         {% mkFloatT (getFLOAT_TYPE $1) (srclocOf $1) }
  | Q_TYPE                             { FixT (uncurry Q  (getQ_TYPE $1)) (srclocOf $1) }
  | UQ_TYPE                            { FixT (uncurry UQ (getQ_TYPE $1)) (srclocOf $1) }
  | 'float'                            { FloatT FP32 (srclocOf $1) }
  | 'double'                           { FloatT FP64 (srclocOf $1) }
  | structid type_application          { StructT $1 $2 ($1 `srcspan` $1) }
  | 'struct' structid type_application { StructT $2 $3 ($1 `srcspan` $3) }

base_type :: { Type }
base_type :
    simple_type       { $1 }
  | '(' ')'           { UnitT ($1 `srcspan` $2) }
  | 'bool'            { BoolT (srclocOf $1) }
  | array_type        { $1 }
  | nat_type          { $1 }
  | tyvar             { TyVarT $1 (srclocOf $1) }
  | '(' base_type ')' { $2 }

nat_type :: { Type }
nat_type :
    INT { NatT ((fromIntegral . snd . getINT) $1) (srclocOf $1) }

array_type :: { Type }
array_type :
    '[' base_type ';' exp ']'
      {% do { n <- natExp $4
            ; return $ ArrT n $2 ($1 `srcspan` $5)
            }
      }
  | '[' base_type ']'
      { ArrT (UnknownT (srclocOf $2)) $2 ($1 `srcspan` $3) }

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

type_application :: { [Type] }
type_application :
    {- empty -}             { [] }
  | '<' base_type_rlist '>' { rev $2 }

maybe_type_application :: { Maybe [Type] }
maybe_type_application :
    {- empty -}             { Nothing }
  | '<' base_type_rlist '>' { Just (rev $2) }

base_type_rlist :: { RevList Type }
base_type_rlist :
    base_type                     { rsingleton $1 }
  | base_type_rlist ',' base_type { rcons $3 $1 }

{------------------------------------------------------------------------------
 -
 - Traits and kinds
 -
 ------------------------------------------------------------------------------}

trait :: { Trait }
trait :
    'Eq'         { EqR }
  | 'Ord'        { OrdR }
  | 'Bool'       { BoolR }
  | 'Num'        { NumR }
  | 'Integral'   { IntegralR }
  | 'Fractional' { FractionalR }
  | 'Bits'       { BitsR }

traits :: { Traits }
traits : trait_rlist { traits (rev $1) }

trait_rlist :: { RevList Trait }
trait_rlist :
    trait                 { rsingleton $1 }
  | trait_rlist '+' trait { rcons $3 $1 }

opt_kind :: { Maybe Kind }
opt_kind :
    {- empty -} { Nothing }
  | ':' 'nat'   { Just NatK }
  | ':' traits  { Just (TauK $2) }
  | ':' error
    {% expected ["`nat'", "a list of traits"] Nothing }

tvk :: { Tvk }
tvk : tyvar opt_kind { ($1, $2) }

tvks :: { [Tvk] }
tvks :
    {- empty -}        { [] }
  | '<' tvks_rlist '>' { rev $2 }

tvks_rlist :: { RevList Tvk }
tvks_rlist :
    tvk                { rsingleton $1 }
  | tvks_rlist ',' tvk { rcons $3 $1 }

{------------------------------------------------------------------------------
 -
 - Statements
 -
 ------------------------------------------------------------------------------}

stm :: { Stm }
stm :
    decl
      { LetS $1 (srclocOf $1) }
  | var_bind '<-' stm_exp
      { let (v, tau) = $1
        in
          BindS v tau $3 (v `srcspan` $3)
      }
  | stm_exp
      { ExpS $1 (srclocOf $1) }

stms :: { [Stm] }
stms :
    stm_rlist { rev $1 }

stm_rlist :: { RevList Stm }
stm_rlist :
    {- empty -}   { rnil }
  | stm_rlist stm { rcons $2 $1 }

-- Statement expressions that need to be terminated with a semicolon.
semi_stm_exp :: { Exp }
semi_stm_exp :
    ID
      { varE (mkVar (varid $1)) }
  | ID maybe_type_application '(' exp_list ')'
      { mkCall (varid $1) $2 $4 ($1 `srcspan` $5) }
  | STRUCTID maybe_type_application '(' exp_list ')'
      { mkCall (structid $1) $2 $4 ($1 `srcspan` $5) }

  | pexp '=' exp
      { AssignE $1 $3 ($1 `srcspan` $3) }

  | inline_ann 'return' exp
     { ReturnE (unLoc $1) $3 ($1 `srcspan` $3) }

  | 'print' exp_list1
      { PrintE False $2 ($1 `srcspan` $2) }
  | 'println' exp_list1
      { PrintE True $2 ($1 `srcspan` $2) }
  | 'error' STRING
      { ErrorE (snd (getSTRING $2)) ($1 `srcspan` $2) }

  | 'emit' exp
      { EmitE $2 ($1 `srcspan` $2) }
  | 'emits' exp
      { EmitsE $2 ($1 `srcspan` $2) }
  | 'take'
      { TakeE (srclocOf $1) }
  | 'takes' exp
      {% do { n <- natExp $2;
            ; return $ TakesE n ($1 `srcspan` $2)
            }
      }

  | 'filter' var_bind
      { let { (v, tau) = $2 }
        in
          FilterE v tau ($1 `srcspan` tau)
      }
  | 'map' vect_ann var_bind
      { let { (v, tau) = $3 }
        in
          MapE $2 v tau ($1 `srcspan` tau)
      }

-- Statement expressions that /do not/ need to be terminated with a semicolon.
nosemi_stm_exp :: { Exp }
nosemi_stm_exp :
    decl 'in' stm_exp
      { LetDeclE $1 $3 ($1 `srcspan` $3) }
  | decl 'in' error
      {% expected ["statement"] Nothing }
  | decl error
      {% expected ["'in'"] Nothing }

  | 'if' exp 'then' stm_exp 'else' stm_exp
      { IfE $2 $4 (Just $6) ($1 `srcspan` $6) }
  | 'if' exp 'then' stm_exp 'else' error
      {% expected ["statement block"] Nothing }
  | 'if' exp 'then' stm_exp %prec IF
      { IfE $2 $4 Nothing ($1 `srcspan` $4) }
  | 'if' exp 'then' error
      {% expected ["statement"] Nothing }
  | 'if' exp error
      {% expected ["then clause"] Nothing }
  | 'if' error
      {% expected ["expression"] Nothing }

  | 'standalone' stm_exp %prec STANDALONE
      { StandaloneE $2 ($1 `srcspan` $2) }
  | 'repeat' vect_ann stm_exp %prec STANDALONE
      { RepeatE $2 $3 ($1 `srcspan` $3) }
  | 'until' exp stm_exp %prec STANDALONE
      { UntilE $2 $3 ($1 `srcspan` $3) }
  | 'while' exp stm_exp %prec STANDALONE
      { WhileE $2 $3 ($1 `srcspan` $3) }
  | unroll_info 'times' exp stm_exp %prec STANDALONE
      { TimesE (unLoc $1) $3 $4 ($1 `srcspan` $4) }
  | unroll_info 'for' var_bind 'in' gen_interval stm_exp %prec STANDALONE
      { let (v, tau) = $3
        in
          ForE (unLoc $1) v tau $5 $6 ($1 `srcspan` $6)
      }

  | '{' stms '}'
      { stmsE $2 }

stm_exp :: { Exp }
stm_exp :
    nosemi_stm_exp
      { $1 }

  | semi_stm_exp ';'
      { $1 }

  | semi_stm_exp error
      {% expected ["';'"] (Just "statement") }

  | stm_exp '>>>' stm_exp
      { ParE AutoPipeline $1 $3 ($1 `srcspan` $3) }
  | semi_stm_exp '>>>' stm_exp
      { ParE AutoPipeline $1 $3 ($1 `srcspan` $3) }

  | stm_exp '|>>>|' stm_exp
      { ParE Pipeline $1 $3 ($1 `srcspan` $3) }
  | semi_stm_exp '|>>>|' stm_exp
      { ParE Pipeline $1 $3 ($1 `srcspan` $3) }

  | '(' stm_exp ')'
      { $2 }

unroll_info :: { L UnrollAnn }
unroll_info :
    {- empty -} { L NoLoc      AutoUnroll }
  | 'unroll'    { L (locOf $1) Unroll }
  | 'nounroll'  { L (locOf $1) NoUnroll }

{------------------------------------------------------------------------------
 -
 - Declarations
 -
 ------------------------------------------------------------------------------}

decl :: { Decl }
decl :
    'let' var_bind '=' exp ';'
      { let { (v, tau) = $2 }
        in
          LetD v tau $4 ($1 `srcspan` $4)
      }
  | 'let' var_bind error
      {% expected ["'='"] Nothing }
  | 'let' var_bind '=' exp error
      {% expected ["';'"] Nothing }

  | 'let' 'mut' var_bind maybe_initializer ';'
      { let { (v, tau) = $3 }
        in
          LetRefD v tau $4 ($1 `srcspan` $4)
      }
  | 'let' 'mut' var_bind error
      {% expected ["initializer", "';'"] Nothing }

  | 'let' 'nat' ID '=' exp ';'
    {% do { n <- natExp $5
          ; return $ LetTypeD (mkTyVar (varid $3)) (Just NatK) n ($1 `srcspan` $5)
          }
    }
  | 'let' 'nat' ID '=' exp error
      {% expected ["';'"] Nothing }
  | 'let' 'nat' ID '=' error
      {% expected ["type of kind nat"] Nothing }

  | 'let' 'comp' maybe_comp_range comp_var_bind '=' stm_exp
      { let { (v, tau) = $4 }
        in
          LetCompD v tau $3 $6 ($1 `srcspan` $6)
      }
  | 'struct' ID tvks '{' field_list '}'
      {% do { addStructIdentifier (getID $2)
            ; return $ StructD (mkStruct (varid $2)) $3 $5 ($1 `srcspan` $6)
            }
      }
  | 'type' ID tvks '=' base_type ';'
      {% do { addStructIdentifier (getID $2)
            ; return $ TypeD (mkStruct (varid $2)) $3 $5 ($1 `srcspan` $6)
            }
      }
  | 'type' ID tvks '=' base_type error
      {% expected ["';'"] Nothing }
  | 'fun' 'external' ID params '->' base_type
      { LetFunExternalD (mkVar (varid $3)) $4 $6 True ($1 `srcspan` $6) }
  | 'fun' 'external' 'impure' ID params '->' base_type
      { LetFunExternalD (mkVar (varid $4)) $5 $7 False ($1 `srcspan` $7) }
  | 'fun' identifier tvks params fun_sig '{' stms '}'
      { LetFunD $2 $3 $4 $5 (stmsE $7) ($1 `srcspan` $8) }

fun_sig :: { Maybe Type }
fun_sig :
    {- empty -}         { Nothing }
  | '->' base_type      { Just $2 }
  | '->' comp_base_type { Just $2 }
  | '->' error          {% expected ["base type"] Nothing }

inline_ann :: { L InlineAnn }
inline_ann :
    {- empty -}   { L NoLoc      AutoInline }
  | 'noinline'    { L (locOf $1) NoInline }
  | 'forceinline' { L (locOf $1) Inline }
  | 'autoinline'  { L (locOf $1) AutoInline }

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

vect_ann_flag :: { (Bool, Range) }
vect_ann_flag :
    comp_range     { (True,  $1) }
  | '!' comp_range { (False, $2) }

-- Comp ranges
comp_range :: { Range }
comp_range :
    '[' exp ',' exp ']'
        {% do { from <- natExp $2
              ; to   <- natExp $4
              ; return (from, to)
            }
        }

maybe_comp_range :: { Maybe Range }
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
  | identifier ':' comp_base_type
      {% do { -- addCompIdentifier (symbol $2)
            ; return ($1, Just $3)
            }
      }
  | identifier ':' error
      {% expected ["ST type"] Nothing }

field_list :: { [(Field, Type)] }
field_list :
    field_rlist { rev $1 }

field_rlist :: { RevList (Field, Type) }
field_rlist :
    {- empty -}           { rnil }
  | field                 { rsingleton $1 }
  | field_rlist ','       { $1 }
  | field_rlist ',' field { rcons $3 $1 }

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
    ID
      { VarBind (mkVar (varid $1)) False Nothing }
  | ID ':' base_type
      { VarBind (mkVar (varid $1)) False (Just $3) }
  | ID ':' comp_base_type
      { VarBind (mkVar (varid $1)) False (Just $3) }
  | ID ':' error
      {% expected ["'ST' or base type"] Nothing }
  | 'mut' ID
      { VarBind (mkVar (varid $2)) True Nothing }
  | 'mut' ID ':' base_type
      { VarBind (mkVar (varid $2)) True (Just $4) }
  | 'mut' ID ':' comp_base_type
      {% fail "Computation parameter cannot be mutable" }

{------------------------------------------------------------------------------
 -
 - Programs
 -
 ------------------------------------------------------------------------------}

program :: { Program }
program :
    {- empty -}        { Program [] [] }
  | imports decl_rlist { Program $1 (rev $2) }

import :: { Import }
import :
    'import' module { Import $2 }
  | 'import' error  {% expected ["module"] Nothing }

imports :: { [Import] }
imports :
    {- empty -}             { [] }
  | import ';' imports { $1 : $3 }

decl_rlist :: { RevList Decl }
decl_rlist :
    decl            { rsingleton $1 }
  | decl_rlist decl { rcons $2 $1 }

{
happyError :: L T.Token -> P a
happyError (L loc t) =
    parserError (locStart loc) (text "parse error on" <+> enquote (ppr t))

getINT         (L _ (T.TintConst T.S x))         = x
getUINT        (L _ (T.TintConst T.U x))         = x
getFLOAT       (L _ (T.TfloatConst x))           = x
getCHAR        (L _ (T.TcharConst x))            = x
getSTRING      (L _ (T.TstringConst x))          = x
getID          (L _ (T.Tidentifier ident))       = ident
getSTRUCTID    (L _ (T.TstructIdentifier ident)) = ident

getINT_TYPE   (L _ (T.Ti w)) = w
getUINT_TYPE  (L _ (T.Tu w)) = w
getFLOAT_TYPE (L _ (T.Tf w)) = w

getQ_TYPE     (L _ (T.Tq i f))  = (i, f)
getUQ_TYPE    (L _ (T.Tuq i f)) = (i, f)

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

mkFloatT :: MonadFail m => Int -> SrcLoc -> m Type
mkFloatT 32 s = return $ FloatT FP32 s
mkFloatT 64 s = return $ FloatT FP64 s
mkFloatT w  _ = faildoc $ text "Cannot handle float width" <+> ppr w

mkTypeName :: String -> Int -> Loc -> Name
mkTypeName s w l = mkName (s ++ show w) l

mkType2Name :: String -> (Int, Int) -> Loc -> Name
mkType2Name s (i, f) l = mkName (s ++ show i ++ "_" ++ show f) l
}
