## ~~r~~ rb-vector

An implementation of vectors backed by a Radix-Balanced Tree.
Initially, I proposed to implement RRB (Relaxed-Radix-Balanced) trees [[1]] instead.
The main difference between them is that
in an RRB tree, nodes are allowed to contain subtrees that are not
completely full. This makes `concat`enation a lot faster (O (log n) vs O(n) for RB trees),
while still retaining bounds on all other operations.


Most of the work of switching from RB trees to RRB trees boils down to changing
the way `get`, `update` and `concat` are implemented. I've finished implementing
`get` and `update`, and I'll do `concat` (in Haskell and Coq) by the next
submission deadline. snoc, cons etc. don't have to change because they can
just be implemented using the new and improved `concat`.

[1]: https://infoscience.epfl.ch/record/213452/files/rrbvector.pdf
