## ~~r~~ rb-vector

An implementation of vectors backed by a Radix-Balanced Tree.
Initially, I proposed to implement RRB (Relaxed-Radix-Balanced) trees [[1]] instead.
However, I could only finish a part of it for this assignment.
The main difference between them is that
in an RRB tree, nodes are allowed to contain subtrees that are not
completely full. This makes `concat`enation a lot faster (O (log n) vs O(n) for RB trees),
while still retaining bounds on all other operations.
I'll finish implementing `concat` (in Haskell and Coq) by the next submission deadline.

[1]: https://infoscience.epfl.ch/record/213452/files/rrbvector.pdf


## Usage

    $ cabal new-test
