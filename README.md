## ~~r~~ rb-vector

An implementation of vectors backed by a Radix-Balanced Tree.
Initially, I proposed to implement RRB (Relaxed-Radix-Balanced) trees [[1]] instead,
but could only finish a part of it.
The main difference between them is that
in an RRB tree, nodes are allowed to contain subtrees that are not
completely full. This makes `concat`enation a lot faster (O (log n) vs O(n) for RB trees),
while still retaining bounds on all other operations.


Most of the work of switching from RB trees to RRB trees boils down to changing
the way `get`, `update` and `concat` are implemented. I've finished implementing
`get` and `update`, and I'll do `concat` (in Haskell and Coq) by the next
submission deadline. snoc, cons etc. don't have to change because they can
just be implemented using the new and improved `concat`.


The branching factor `m` is global constant (default: 4). Here's a list of vector
operations this supports:


| Op                   | Time complexity   |
|    :---:             |     :---:         |
| indexing ((!), (!?)) | O(log_m n)        |
| update               | O(m * (log_m n))  |
| cons                 | O(m * (log_m n))  |
| snoc                 | O(m * (log_m n))  |
| concat               | O(n)              |
| empty                | O(1)              |
| toList               | O(n)              |
| fromList             | O(n)              |
| length               | O(1)              |


[1]: https://infoscience.epfl.ch/record/213452/files/rrbvector.pdf


## Usage

Run tests with:

    $ cabal new-test

or

    $ stack test


## Quick links

1. [Data.RRB.Vector.hs](https://github.com/ckoparkar/rrb-vector/blob/master/src/Data/RRB/Vector.hs)
2. [Tests](https://github.com/ckoparkar/rrb-vector/blob/master/tests/Main.hs)
3. [RRB-Trees paper][1]
4. This [blogpost](https://hypirion.com/musings/understanding-persistent-vector-pt-1) is also a good read.
