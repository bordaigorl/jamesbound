README
======

This repository contains an Haskell package, `picalc`, and an executable `jb`, short for "James Bound".
It defines data structures and functions for the representation of the
syntax and operational semantics of the π-calculus, and its *depth-bounded* fragment (hence the name).

For more information about π-calculus see
    <https://en.wikipedia.org/wiki/Pi_calculus>.

Other (more theoretical) references for a quick introduction are

 * Milner, R. 1993. *The polyadic π-calculus: a tutorial.*
   Logic and Algebra of Specification (1993).
   Available at <http://hdl.handle.net/1842/6050>.
 * Meyer, R. 2008. *On Boundedness in Depth in the π-calculus.*
   IFIP TCS (2008).
   Available at <http://concurrency.informatik.uni-kl.de/documents/meyer_bounded_depth_2008.pdf>

The analysis implemented by James Bound is a variation over the type system described in

 * D'Osualdo, E., Ong, L. 2015. *A Type System for proving Depth Boundedness in the π-calculus.*
   Available at <http://arxiv.org/abs/1502.00944>

This module is not intended to define a π-calculus style embedded domain
specific language but rather to represent, transform, analyse and interpret
π-calculus terms. For this reason the interpretation is not tuned for speed and
it is not meant to be used for executing systems but rather to explore the
semantics of the terms.

The current version is to be considered *experimental* and simply a playground for experimenting with π-calculus.


## License

This code is released under GPLv2 but in the spirit of the [CRAPL][]:

> Science thrives on openness.
>
> In modern science, it is often infeasible to replicate claims without
> access to the software underlying those claims.
>
> Let's all be honest: when scientists write code, aesthetics and
> software engineering principles take a back seat to having running,
> working code before a deadline.
>
> So, let's release the ugly.  And, let's be proud of that.


## Compilation

The `jb` program can be compiled by running

    cabal build

from the top directory of the repository.


## Syntax of the language

`PiCalc` implements a variant of polyadic π-calculus.
Its syntax is defined in the [wiki] and the `SYNTAX.md` file.

[CRAPL]: http://matt.might.net/articles/crapl/
[wiki]: https://github.com/bordaigorl/jamesbound/wiki