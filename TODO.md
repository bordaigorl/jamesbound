# IDEAS

## New Syntax

Definitions:

+ Interpret definitions P[x]:=t exactly as P?x.t
+ there is a global implicit parallel, all defs/naked terms are in parallel
+ layout rules
+ local definitions with `where` (removes need for globals)

Channel names:

+ A name can be a record (named tuple) so that you can pass around logically grouped names under a single "variable". Example: you can have two counters each with an `inc` and a `dec` channel, instead of passing around `inc1` `dec1` and `inc2` and `dec2`, you can have `count1` and `count2` each with two indexes `inc` and `dec`.
+ Introduce indexing notation `name@subname` (or `subname@name`?)
+ Formal arguments specify indexes: `count@[inc, dec]` (or `count@{inc, dec}`)
+ Macros can help define "types" as in `#define Counter {inc, dec}` and then `c@COUNTER` 
+ Choice (1 is easier):
  1. you can see this as syntactic sugar `c@[a,b]` → `c_a, c_b` (order counts) or
  2. indexes could be ids so they must match: `c@{a,b}` ≡ `c@{b,a}`

## New REPL

+ JB REPL in explore-mode:
   - stack-based model to naturally support depth-first exploration
   - initially top of stack is `zero` (equivalent to empty stack i.e. stack never empty)
   - typing a π-term puts it in parallel with top of stack (can be a def, can be initial term, see new syntax)
   - executing a command usually manipulates the top of the stack
   - some commands (e.g.: run) push new terms on the stack
   - some others (e.g.: backtrack) pop

  Available commands: 

   - every command can be ended with `:to <file>` to redirect the output to a file
   - every command has a `?` and a `!` variant:
      * `:cmd?` shows an help message
      * `:cmd!` executes the command every time the top changes (push or pop)
      * `:!` prints what's set to happen
      * `:! rem [N|all]` removes the selected action
      * `:top` reruns the banged commands
   - a config file `.jbc` is read and executed:
     can define standard symbols, setup aliases and setup which banged commands to set
   - `:alias <name> <cmd>...` 
   - `:q` / `:quit`
   - `:?` / `:help` / `:h`
   - `:D` / `:debug` shows guts of stack / term
   - `:stats`
   - `:set <opt> [<value>]` setting options
   - `:def <definitions>` add definitions to the environment
   - `:defs` shows the current environment
   - `:e` / `:edit` readline with top as initial text
   - `:d` / `:depth` shows depth of term
   - `:nest` and similar commands show measurements of the top
   - `:covers <term> [<term>]` and `:congruent`
   - `:run [<strategy>] [#steps]`
   - `:succ :successors` shows a list of successors (with indexes)
   - `:step <which>` push selected successor. `<which>` should be an index
   - `:back [<N>]` backtrack by popping
   - `:render <format> [<opt>]` shows the term in the selected format
   - `:print` renders top with standard options
   - `:clear` resets to an empty stack
   - `:load` loads defs and uses initial term as inital text for readline
   - `:save` saves the current definitions + top to file
   - `:trace [<opt>]` dumps the stack 

+ Reintroduce pvar parametrisation in PiAST and introduce

        data ParsedPVar = PPVar{pvarStr :: String, pvarLoc :: SourcePos}
        data ParsedName = PName{nameStr :: String, nameLoc :: SourcePos}

  so that in Manipulations we can give good error feedback (and generate
  ParseError instead of String for errors <http://hackage.haskell.org/packages/archive/parsec/2.1.0.1/doc/html/Text-ParserCombinators-Parsec-Error.html>)

+ Rewrite PiName as

        data PiName = Global {ctxt=PiPVar, origin=SourcePos, static::String}
                    | Local  {ctxt=PiPVar, origin=SourcePos, static::String, unique :: NameId}

+ Create classes for Process and Forms (see below).
  Find a general structure for redexes or hide redex types completely (because
  dependent on process implementation)?
  It seems we need GADT or functional dependencies...I'd rather avoid them.

+ *NOT SURE* Complete rewrite of Process.hs: represent redexes as

      data Redex = SynchAt PiPos PiPos NameSubst
                   -- ^     In    Out      σ
                 | TauAt PiPos
                 | UnfoldAt PiPos NameSubst
      type PiPos = PiPos Int Int
      -- ^ seq term index, index of alternative
      --OR (better for performance?)
      type PiPos = PiPos PiFactor PiTerm
      -- ^ selected seq term, selected portion of redex

  This enables an easy notion of independence

      (PiPos i j _) `independent` (PiPos i' j' _) = i /= i'

# TODO

+ Convert should be able to take term from param or from stdin

+ Use View patterns to pattern match any → StdNFTerm/PiTerm

+ Migrate to `Text.PrettyPrint.Leijen` for prettier output

+ Since bound names of a std are often used, why not store them in a
  `boundNames` field of `StdNF`?

+ Refactor StdNF.hs: find place for conversion functions and depth
  Combine with Term, rename to NormalForms and introduce the class Term?

+ Pretty options
    * latex

+ Commandline options:
    * Global options: controlling pretty printing, verbosity...
    * Modes:
      - *explore*: interactive exploration of terms
      - *cat*: check syntax of term, pretty print preprocessed code in different
        formats (dot, stdnf, restrf, no-confl).
      - *analyse*: generate cover, check for depth boundedness...

+ Conversions:
  * definitional NF (everything in StdNF + ProcNames for every step)
  * bang NF (everything in StdNF + PVar -> PiName and defs inlined as bangs)
  * javascript (for export to picalc simulator)

+ Consider general classes for PiTerm/StdNF/... with
  isSeq...allNames...conversions?

Structure the main program as a reader/state monad transformer on IO holding the
options. The `main` would just parse the arguments and exec the monad
initialising the options.
A `Frontend` module would define the monadic actions + CmdArgs.


## Sat for Haskell

* <https://github.com/niklasso/minisat-haskell-bindings>
* <http://hackage.haskell.org/package/satchmo>
* <http://hackage.haskell.org/package/sat-micro-hs>
* <http://hackage.haskell.org/package/incremental-sat-solver>
* <https://github.com/dbueno/funsat>
* <http://minisat.se/>

