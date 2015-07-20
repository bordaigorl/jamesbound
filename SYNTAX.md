# Syntax of the language

`PiCalc` is a variant of polyadic π-calculus.
Its syntax is defined as follows.

Comments are C style starting with `\\` or enclosed in `/*` `*/`.

*Names* (channel names, atomic) are identifiers starting with a lower case
letter or `_` and containing only letters or `_` or `'`.

*Process identifiers* are alphanumeric and can contain `_` but must start with
an upper case letter.

You can group sub-expressions using `()`.

Most operators have alternative syntax to accomodate four main styles:

 3. Ascii
 4. Unicode
 1. Milner style prefixes
 2. Hoare style prefixes

The unicode style is the preferred and uses unicode symbols for some operators
for improved readability.
The ascii versions are mantained for portability.

### Prefixes

Input prefixes can be written as:

```
name(x1,...,xn).term  // Milner style
name?(x1,...,xn).term // Hoare style
// arity 0
name().term
name?.term
// arity 1
name(x).term
name?x.term
```

Output prefixes can be written as:

```
name<x1,...,xn>.term // Milner style
name⟨x1,...,xn⟩.term // Milner Unicode style
name!(x1,...,xn)     // Hoare style
// arity 0
name<>.term
name⟨⟩.term
name!.term
//arity 1
name<x>.term
name⟨x⟩.term
name!x.term
```
Since in some fonts `⟨⟩` could be difficult to tell apart from `()` we
discourage the Milner Unicode style for this operator.

Tau prefixes can be written using unicode `τ.term` or ascii `tau.term` style.

### Inactive process

The inactive process is written as `0` or `zero`.
Hence `zero` cannot be used as a name.

### Restrictions

The restriction operator can be written in the following ways:

```
ν(x1,...,xn). term      // Unicode
new (x1,...,xn). term   // Ascii
// arity 1
νx.term
new x.term
```

### Parallel

The parallel operator can be written as

```
term ‖ term   // Unicode
term | term   // Ascii
```

### Alternatives (Sums)

The sum operator `+` can glue together prefixed terms:

```
π1.term + ... + πn.term
```

where `πi` is either an output, an input or a tau prefix.

### Definitions

You can define a process with

```
Proc[x1,...,xn] := term
```

where `Proc` is a process identifier, `x1,...,xn` are the arguments, which must
be distinct; the only free names in `term` are the arguments (apart from
[global names](global-names), see below).

In any term of the program you can "call" a process with the expression
`Proc[x1,...,xn]`. Obviously, when calling the arguments do not need to be
distinct. Each process identifier can be defined only once and the identifier is
global.
What happens when calling `P[x,y,z]` with a definition `P[a,b,c] := term` is
that in one (internal) step you rewrite `P[x,y,z]` to `term[x/a,y/b,z/c]` where
`x/a` means substituting `x` for `a`.

In the argument list, both in the call and the definition, the square brackets
can be omitted when the list is empty, eg. `P[]` is the same as `P`.

Note that calls to processes with an argument list of the wrong length will
result in a syntax error.

When a process with no definition is called, the definition `P[...] := 0` is
used.

### Recursive behaviour

Any process identifier is available in the body of a definition.
This means that it is possible to define processes with recursive behaviour like

```
P[a,x] := a!x | νy.P[a,y]
```

The bang operator `*(P)` is a shortcut for a call to `Q` with implicit
definition `Q := P | Q`; hence `*(P)` rewrites in one step to `P | *(P)`.


### Global names

In order to ease writing code sharing a lot of global names, it is possible to
exclude some variables from the arguments of a process definition by declaring
them as global names, at the beginning of the program:

```
#global a b;

νx.P[x]

P[x] := a!x.P[b] + b?y.P[y]
```

Note that `νa.P[a]` does not identify `a` in the body of `P` with the restricted
one but with the global (free) one; in other words it rewrites to
`νa1.a!a1.P[b] + b?y.P[y]`.

### Program structure

A complete program has the following structure:

```
<prog>       ::= [<globals>] <term> {<definition>}
<globals>    ::= "#global" {<name>} ";"
<definition> ::= <proc-id>["[" [<name> {, <name>}] "]" ] ":=" <term>

<term> ::= 0 | zero
        |  "(" <term> ")"
        | <term> <par-op> <term>
        | <prefix> "." <term> {"+" <prefix> "." <term>}
        | <new-op> <namelist-par> "." <term>
        | <proc-id>["[" [<name> {, <name>}] "]" ]
        | "*" <term>
<namelist-par> ::= <name> | "(" <name> {, <name>} ")"
```

The term specified after the optional `#global` declaration is the starting process.

Here's an example program modelling a stack:

```
#global pu po;

νbot.Stack[pu, po, bot] | Client[output]

Client[res] := pu<a>.pu<b>.pu<c>.po<res>.po<res>

Stack[push, pop, next] :=
    push(top).
        (νnext'.( next'<top, next> | Stack[push, pop, next'] ))
  + pop(r).
        next(top, next').(r<top> | Stack[push, pop, next'])
```
