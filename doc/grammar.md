# Kyllini Language Grammar

* Terminals are written as single- or double-quoted strings, e.g.,`'if'` and `"'1"`
* Non-terminals are written in angle brackets, e.g., `<decl>`
* `ε` denotes the empty production
* `<foo>?` denotes an optional `<foo>`
* `<foo>*` denotes zero or more `<foo>`s
* `(<foo> ';' ...)*` denotes zero or more `<foo>`s separated by `';'`
* `<foo>+` denotes one or more more `<foo>`s
* `(<foo> ';' ...)+` denotes one or more more `<foo>`s separated by `';'`
* We use capitals to denote several syntactic classes:
  * `ID`: an identifier, which consists of alphanumeric characters and '_'.
  * `STRUCT`: a previously-declared `struct` identifier.
  * `INT`: integer literal, e.g., `128`
  * `FLOAT`: floating-point literal, e.g., `3.14`
  * `STRING`: string literal, e.g., `"foobar\n"`
  * `TYVAR`: a type variable

## Programs and top-level declarations

```
program ::=
   ('import' <module> ';')*
   <decl>+

decl ::=
   'let' ID (':' <base-type>)? '=' <exp> ';'
 | 'let' 'mut' ID (':' <base-type>)? ('=' <exp>)? ';'
 | 'struct' ID <tvks> '{' ID ':' <base-type> ',' ... '}'
 | 'type' ID <tvks> '=' <base-type> ';'
 | 'fun' 'external' 'impure'? ID '(' (<param> ',' ...)* ')' '->' <base-type>
 | 'fun' ID <tvks> '(' (<param> ',' ...)* ')' ('->' <type>)? '{' <stms> '}'
 | 'let' 'comp' <range>? ID (':' <comp-base-type>)? '=' <stm-exp> ';'

param ::=
   ID
 | ID ':' <base-type>
 | ID ':' <comp-base-type>
 | 'mut' ID
 | 'mut' ID ':' <base-type>
 | 'mut' ID ':' <comp-base-type>
```

## Expressions

```
scalar ::=
   'true'
 | 'false'
 | "'0"
 | "'1"
 | INT
 | FLOAT
 | STRING

path-exp ::=
   ID
 | <path-exp> '.' ID
 | <path-exp> '[' <exp> ']'
 | <path-exp> '[' <exp> ':' <exp> ']'

aexp ::=
   <scalar>
 | '[' (<aexp> ',' ...)+ ']'
 | <path-exp>
 | <aexp> '+' <aexp>
 | <aexp> '-' <aexp>
 | <aexp> '*' <aexp>
 | <aexp> '/' <aexp>
 | <aexp> '%' <aexp>
 | <aexp> '**' <aexp>
 | <aexp> '<<' <aexp>
 | <aexp> '>>' <aexp>
 | <aexp> '&' <aexp>
 | <aexp> '|' <aexp>
 | <aexp> '^' <aexp>
 | <aexp> '==' <aexp>
 | <aexp> '!=' <aexp>
 | <aexp> '<' <aexp>
 | <aexp> '>' <aexp>
 | <aexp> '<=' <aexp>
 | <aexp> '>=' <aexp>
 | <aexp> '&&' <aexp>
 | <aexp> '||' <aexp>
 | '-' <aexp>
 | 'not' <aexp>
 | '~' <aexp>
 | 'length' <aexp>
 | <simple-type> '(' <exp> ')'
 | STRUCT <type-application> '{' (ID '=' <exp> ',' ...)+ '}'
 | 'struct' STRUCT <type-application> '{' (ID '=' <exp> ',' ...)+ '}'
 | ID '(' (<exp> ',' ...)* ')'
 | '(' <exp> ')'

exp ::=
   <aexp>
 | 'if' <exp> 'then' <exp> 'else' <exp>
 | 'let' ID (':' <base-type>)? '=' <exp> 'in' <exp-or-stms>
 | 'let' 'mut' ID (':' <base-type>)? ('=' <exp>)? 'in' <exp-or-stms>
```

## Statements

```
exp-or-stms ::=
   <exp>
 | '{' (<stm> ';' ...)* '}'

stm ::=
   <decl>
 | ID (':' <base-type)? '<-' <stm-exp> ';'
 | <stm-exp>

stm-exp ::=
   <decl> 'in' <stm-exp>
 | ID ';'
 | ID '(' (<exp> ',' ...)* ')' ';'
 | <path-exp> '=' <exp> ';'
 | 'if' <exp> 'then' <stm-exp> 'else' <stm-exp>
 | 'if' <exp> 'then' <stm-exp>
 | 'repeat' <vect-ann> <stm-exp>
 | 'until' <exp> <stm-exp>
 | 'while' <exp> <stm-exp>
 | <unroll-info> 'times' <exp> <stm-exp>
 | <unroll-info> 'for' ID (':' <base-type>)? 'in' <gen-interval> <stm-exp>
 | 'return' <exp> ';'
 | 'print' (<exp> ',' ...)+ ';'
 | 'println' (<exp> ',' ...)+ ';'
 | 'error' STRING ';'
 | 'emit' <exp> ';'
 | 'emits' <exp> ';'
 | 'take' ';'
 | 'takes' <const-int-exp> ';'
 | 'filter' ID (':' <base-type>)? ';'
 | 'map' <vect-ann> ID (':' <base-type>)? ';'
 | '{' (<stm> ';' ...)* '}'
 | <stm-exp> '>>>' <stm-exp>
 | <stm-exp> '|>>>|' <stm-exp>
 | '(' <stm-exp> ')'

unroll-info ::=
    ε
 | 'unroll'
 | 'nounroll'

vect-ann ::=
    ε
 | '[' INT ',' INT ']'
 | '!' '[' INT ',' INT ']'
 | '<=' '[' INT ',' INT ']'
 | '<=' '!' '[' INT ',' INT ']'
```

## Types

```
simple-type ::=
   'bit'
 | 'int' | 'int8' | 'int16' | 'int32' | 'int64' | 'iN'
 | 'uint' | 'uint8' | 'uint16' | 'uint32' | 'uint64' | 'uN'
 | 'float' | 'double' | 'f32' | 'f64'
 | STRUCT <type-application>
 | 'struct' STRUCT <type-application>

base-type ::=
   simple-type
 | '(' ')'
 | 'bool'
 | <array-type>
 | TYVAR
 | '(' <base-type> ')'

array-type ::=
   '[' <base-type> ';' 'length' '(' ID ')' ']'
 | '[' <base-type> ';' <exp> ']'
 | '[' <base-type> ']'

comp-base-type ::=
   'ST' <index-type> <base-type> <base-type>
 | '(' <comp-base-type> ')'

index-type ::=
   'T'
 | 'C' <base-type>
 | '(' <index-type> ')'

type-application ::=
   ε
 | '<' (<base-type> ',' ...)+ '>'
```

## Generics

```
tvks ::=
   ε
 | '<' ID (':' <traits>)? ',' ... '>'

traits ::= trait '+' ...

trait :=
   'Eq'
 | 'Ord'
 | 'Bool'
 | 'Bits'
 | 'Num'
 | 'Integral'
 | 'Fractional'
```
