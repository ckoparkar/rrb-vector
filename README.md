## ~~r~~ rb-vector


## Verification

I've stuck with RB trees instead of RRB trees like I proposed earlier. Also,
I cheated in the Coq implementation a little bit. The `snoc_Bottom` function
in [Vector2.v](proofs/Vector2.v) exactly matches the Haskell version, and also
the paper. Notice that it accepts a `fuel : nat` in addition to all the
usual arguments. That's because Coq cannot determine that the recursive
call on rightmost subtree (in the Node case) is in fact primitive recursive.
So the function is defined to be structurally recursive on this nat instead.
I kept trying to prove things with this for a long time but ran into some
problems. Specifically, I think I couldn't prove, without using an Axiom, that
all snoc_Bottom's will always have enough fuel to finish executing. Also,
becuase it's not structurally recursive on the tree, unfold wouldn't work
in the usual way in the proofs and so on. I didn't get far with
`Program Fixpoint` either; I'm having trouble remembering the exact details of
where I was stuck. I briefly considered going the full 'Well-Founded Recursion'
route, but decided against it.


On Friday, I gave up and changed the implementation to grow the trees toward
the left. This was the cheat I was referring to earlier. So `snoc` actually
works like `cons`, and everything else is reversed too.
For example, this is what a tree with 20 elements looks like:


```Coq

Definition tree20 : tree nat :=
  Node 2 [20 ; 16]
         [ Node 1 [4]
                [ Leaf [4 ; 3 ; 2 ; 1] [20 ; 19 ; 18 ; 17]
                ]
         ; Node 1 [16 ; 12 ; 8 ; 4]
                [ Leaf [4 ; 3 ; 2 ; 1] [16 ; 15 ; 14 ; 13]
                ; Leaf [4 ; 3 ; 2 ; 1] [12 ; 11 ; 10 ; 9]
                ; Leaf [4 ; 3 ; 2 ; 1] [8 ; 7 ; 6 ; 5]
                ; Leaf [4 ; 3 ; 2 ; 1] [4 ; 3 ; 2 ; 1]
                ]
       ].

```

Along with snoc I updated `get` accordingly. So `get 0 tree20 100` still
returns 1, not 20. As you would expect, this made the proofs a lot simpler.
See [Vector3.v](proofs/Vector3.v) for the new implementation and proofs.


I couldn't get a lot done -- here are some of the theorems I could prove:

1. The length of a vector is 0 iff it's empty (`vec_length_0_E`).
2. After `snoc vec a`, a is in the vector (`snoc_In_Vec`).
3. If a vector has space, snoc_Bottom never "fails" (`snoc_Bottom_not_E`).
4. After snoc'ing one element into a vector, it's length increases by 1
   (`snoc_length`).
5. snoc maintains the invariants of an RB tree (`snoc_is_RRB`).
6. snoc relates to (val :: ls) (has 1 admit in it) (`snoc_relate`).


7. get_relate ... ?



Also, in the presentation, I briefly mentioned a problem with the induction
principle that Coq generates by default for the `tree` datatype --
"because we use the type we are defining as an argument to a parameterized type family".
Spefically, `tree_ind` doesn't say that if a proposition P holds for a `Node`,
it also holds for all the sub-trees (list (tree A)) of that Node. At the time,
I had not finished these proofs, so I  couldn't point to any specific place
where this becomes important. However, now I've learnt that a lot of these
proofs would be impossible to write without the stronger induction principle,
`tree_ind'`, that I copied from Chlipala's [book](http://adam.chlipala.net/cpdt/html/InductiveTypes.html)
(see Nested Inductive Types), `snoc_is_RRB` in particular. I've marked
one such goal in that proof.



## Haskell implementation

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
