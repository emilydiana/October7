---
fulltitle: Red Black Trees
date: October 7, 2019
---

This module implements a persistent version of a common balanced tree
structure: Red Black trees.

It serves as both a demonstration of a purely functional data structure
and as an additional use-case for QuickCheck.

> {-# LANGUAGE InstanceSigs #-}
> {-# LANGUAGE ScopedTypeVariables #-}
> {-# LANGUAGE TypeApplications #-}
> {-# LANGUAGE DeriveFoldable #-}
> module RedBlack where

RedBlack trees implement the Set interface.

> import Persistent

If you have trouble loading the `Persistent` module, you may need to change
directories in ghci and then reload.

      Prelude> :cd ~/552/lectures
      Prelude> :r

We'll make some standard library functions available for this implementation.

> import qualified Data.Maybe as Maybe
> import qualified Data.List  as List
> import qualified Data.Foldable as Foldable

And we'll use QC for testing.

> import Test.QuickCheck hiding (elements)
> import qualified Test.QuickCheck as QC (elements)
> import Control.Monad (when)

Tree Structure
--------------

A red-black tree is a binary search tree where every node is marked with a
color (red `R` or black `B`).  For brevity, we will abbreviate the standard
tree constructors `Empty` and `Branch` as `E` and `N`. (The latter stands for
*node*.) Using the `DeriveFoldable` language extension we can automatically
make this tree an instance of the `Data.Foldable` type class.

If it has been a while since you have seen red black trees, [refresh your
memory](https://en.wikipedia.org/wiki/Red%E2%80%93black_tree).


> data Color = R | B deriving (Eq, Show)
> data RBT a = E | N Color (RBT a) a (RBT a) deriving (Show, Foldable)

Every red-black tree has a color, determined by the following function.

> color :: RBT a -> Color
> color (N c _ _ _) = c
> color E = B

Red Black trees must satisfy the following four invariants.

  1. Empty trees are black

  2. The root (i.e. the topmost node) of a nonempty tree is black 

  3. From each node, every path to an `E`
     has the same number of black nodes

  4. Red nodes have black children

* The first invariant is true by definition of the `color` function above. The
  others we will have to maintain as we implement the various tree
  operations. 

* Together, these invariants imply that every red-black tree is "approximately
  balanced", in the sense that the longest path to an `E` is no more than
  twice the length of the shortest.

* From this balance property, it follows that all operations will run in
  `O(log_2 n)` time.

Sample Trees
------------

Here are some example trees; only the first one below is actually a red-black
tree. The others violate the policy in some way.

> good1 :: RBT Int
> good1 = N B (N B E 1 E) 2 (N B E 3 E)

Here is one with a red Root.

> bad1 :: RBT Int
> bad1  = N R (N B E 1 E) 2 (N B E 3 E)

Here's one that violates the black height requirement.

> bad2 :: RBT Int
> bad2  = N B (N R E 1 E) 2 (N B E 3 E)

Now define a red-black tree that violates invariant 4.

> bad3  :: RBT Int
> bad3 = N B (N R (N R E 1 E) 2 (N R E 3 E)) 4 (N B E 5 E) 

Now define a red-black tree that isn't a binary search tree (i.e. the *values*
stored in the tree are not in strictly increasing order).

> bad4 :: RBT Int
> bad4 = N B (N B E 3 E) 2 (N B E 1 E) 

All sample trees, plus the empty tree for good measure.

> trees :: [(String, RBT Int)]
> trees = [("good1", good1),
>          ("bad1", bad1),
>          ("bad2", bad2),
>          ("bad3", bad3),
>          ("bad4", bad4),
>          ("empty", E)]


Checking the RBT invariants
---------------------------

We can write quickcheck properties for each of the invariants.

1. The empty tree is black. (This is actually a unit test).

> prop_Rb1 :: Bool
> prop_Rb1 = color E == B

2. The root of the tree is Black. (This subsumes the previous invariant.)

> prop_RB2 :: RBT Int -> Bool
> prop_RB2 t = color t == B

3.  For all nodes in the tree, all downward paths from the node to `E` contain
the same number of black nodes. (Make sure that this test passes for `good1` and
fails for `bad2`.)

> prop_RB3 :: RBT Int -> Bool
> prop_RB3 t = case t of
>   E -> True
>   (N c a x b) -> bh a == bh b 

> -- | calculate the black height of the tree
> bh :: RBT a -> Int
> bh E = 1
> bh (N c a x b) = bh a + (if c == B then 1 else 0)

4. All children of red nodes are black. 

> prop_RB4 :: RBT Int  -> Bool
> prop_RB4 (N R (N R _ _ _) _ _) = False
> prop_RB4 (N R _ _ (N R _ _ _)) = False
> prop_RB4 (N _ a _ b) = prop_RB4 a && prop_RB4 b
> prop_RB4 E = True

5. And satisfies the binary search tree condition[4]. 

> prop_BST :: RBT Int -> Bool
> prop_BST = orderedBy (<) . Foldable.toList
>
> orderedBy :: (a -> a -> Bool) -> [a] -> Bool
> orderedBy op (x:y:xs) = x `op` y && orderedBy op (y:xs)
> orderedBy op _ = True

Note that we get the `toList` operation for the tree *for free* using the
`DeriveFoldable` extension. All we need is a predicate that determines whether
the elements of the tree are strictly ordered.

Testing the tests
-----------------

Take a moment to try out the properties above on the sample trees by running
the `testProps` function in ghci. The good trees should satisfy all of the
properties, whereas the bad trees should fail at least one of them.

> testProps :: IO ()
> testProps = mapM_ checkTree trees  where
>    checkTree (name,tree) = do
>      putStrLn $ "******* Checking " ++ name ++ " *******"
>      quickCheck $ once (counterexample "RB2" $ prop_RB2 tree)
>      quickCheck $ once (counterexample "RB3" $ prop_RB3 tree)
>      quickCheck $ once (counterexample "RB4" $ prop_RB4 tree)
>      quickCheck $ once (counterexample "BST" $ prop_BST tree)

For convenience, we can also create a single property that combines all four
of the above together. The `counterexample` function reports which part of the
combined property fails.

> prop_RBT :: RBT Int -> Property
> prop_RBT t = counterexample "RB2" (prop_RB2 t) .&&.
>              counterexample "RB3" (prop_RB3 t) .&&.
>              counterexample "RB4" (prop_RB4 t) .&&.
>              counterexample "BST" (prop_BST t)

Arbitrary Instance
------------------

Our goal is to use quickcheck to verify that the RBT-based set operations
preserve these invariants. To do this, we will need an arbitrary instance for
the `RBT` type. However, because we want to verify that `prop_RBT` is an
*invariant* of our data structure, we will only want to test our operations on
trees that satisfy this invariant. And not many do!

Therefore, we will make sure that our `RBT` generator only produces valid
red-black trees. How can we do this?

We'll start with a generic generators for sets, based on `insert` and `empty`.
Below, we use the operator form of `fmap`, written `<$>` to first generate an
arbitrary list of values, and then fold over that list, inserting them into
the set one by one.

> genSet :: forall a s. (Ord a, Arbitrary a, Set s) => Gen (s a)
> genSet = foldr insert empty <$> (arbitrary :: Gen [a])

We can use this generator directly for RBTs. If our `insert` function is
preserves this invariant, then we will only generate valid red-black trees. If
not, then running quickcheck with `prop_RBT` should fail.

> instance (Ord a, Arbitrary a) => Arbitrary (RBT a)  where
> 
>    arbitrary          :: Gen (RBT a)
>    arbitrary          = genSet
>
>    shrink             :: RBT a -> [RBT a]
>    shrink E           = []
>    shrink (N _ l _ r) = [blacken l,blacken r]

The shrink function is used by quickcheck to minimize counterexamples. The
idea of this function is that it should, when given a tree, produce some
smaller tree. Both the left and right subtrees of a wellformed red-black tree
are red-black trees, as long as we make sure that their top nodes are black.
We can ensure that a tree is black using the following simple function.

> blacken :: RBT a -> RBT a
> blacken E = E
> blacken (N _ l v r) = N B l v r

What other properties should we test?

We also want to know that the delete operation satisfies the RBT
invariants. We'll specify this with two different cases, one for when the
element to delete is not a member of the set (this happens frequently for
randomly generated sets and elements) and one where the element to delete is a
member of the set (we can randomly pick one of the set members to delete).

> prop_RBT_delete_nonmember :: Int -> RBT Int -> Property
> prop_RBT_delete_nonmember x t =
>   not (member x t) ==>
>   prop_RBT (delete x t)

> prop_RBT_delete_member :: RBT Int -> Property
> prop_RBT_delete_member t =
>   forAll (QC.elements (elements t)) (\x -> prop_RBT (delete x t)) 



All the tests together
----------------------

> main :: IO ()
> main = do

Make sure that insert preserves the red-black tree invariant

>   quickCheck prop_RBT

Make sure that delete preserves the red-black tree invariant

>   quickCheck prop_RBT_delete_nonmember
>   quickCheck prop_RBT_delete_member

Make sure the RBT is a set (according to the properties defined in `Persistent`)

>   quickCheck $ prop_empty  @RBT
>   quickCheck $ prop_insert @RBT
>   quickCheck $ prop_insert_inequal @RBT
>   quickCheck $ prop_elements @RBT

Add other set properties that you defined in the `Persistent` module.

>   quickCheck $ prop_myproperty @RBT

Set Instance
--------------

We now just need to implement the methods of the `Set` class for this data
structure.  The `empty`, `member` and `elements` operations are
straightforward. See if you can fill in this last definition (HINT: the RBT is
`Foldable`).

> instance Set RBT where

>   empty :: RBT a
>   empty = E 

>   member :: Ord a => a -> RBT a -> Bool
>   member x E = False
>   member x (N _ a y b)
>     | x < y     = member x a
>     | x > y     = member x b
>     | otherwise = True

>   elements :: Ord a => RBT a -> [a]
>   elements = Foldable.toList 


However, insertion and deletion are, of course, a bit trickier. We'll define
them both with the help of auxiliary functions, which can violate the
red-black invariants temporarily. To make sure that everything works out, we
`blacken` the result of these helper functions to make sure that property 2
holds.

>   insert :: Ord a => a -> RBT a -> RBT a
>   insert x t = blacken (ins x t)

>   delete :: Ord a => a -> RBT a -> RBT a
>   delete x t = blacken (del x t) 

Implementation of insert
------------------------

Below, we'll only consider the implementation of `ins`. For `del`, see
the end of the lecture.

The recursive function `ins` walks down the tree until...

> ins :: Ord a => a -> RBT a -> RBT a

... it gets to an empty leaf node, in which case
it constructs a new (red) node containing the
value being inserted...

> ins x E = N R E x E

... finds the correct subtree to insert the value, or discovers that the value
being inserted is already in the tree (in which case it returns the input
unchanged):

> ins x s@(N c a y b)
>   | x < y     = balance (N c (ins x a) y b)
>   | x > y     = balance (N c a y (ins x b))
>   | otherwise = s


Note that this definition breaks the RBT invariants in two ways --- it could
create a tree with a red root (when we insert into an empty tree), or create a
red node with a red child (when we insert into a subtree).  The former case is
taken care of with the call to `blacken` at the toplevel definition of the
`insert` function. To repair the second situation, we need to rebalance the
tree.

Balancing
---------

In the recursive calls of `ins`, before returning the new tree, we may need to
*rebalance* to maintain the red-black invariants. The code to do this is
encapsulated in a helper function `balance`.

* The key insight in writing the balancing function is that we do not try to
rebalance as soon as we see a red node with a red child. That can also be
fixed just by blackening the root of the tree, so we return this tree as-is.
(We call such trees, which violate invariants two and four only at the root
"infrared").

The real problem comes when we've inserted a new red node between a black
parent and a red child.

* i.e., the job of the balance function is to rebalance trees with a
black-red-red path starting at the root. Since the root has two children and
four grandchildren, there are four ways in which such a path can happen.


           B             B           B              B
          / \           / \         / \            / \
         R   d         R   d       a   R          a   R
        / \           / \             / \            / \
       R   c         a   R           R   d          b   R
      / \               / \         / \                / \
     a   b             b   c       b   c              c   d

* The result of rebalancing maintains the black height by converting
to a red parent with black children.

                                     R
                                   /   \
                                  B     B
                                 / \   / \
                                a   b c   d

In code, we can use pattern matching to directly identify the four trees above
and rewrite them to the balanced tree.  All other trees are left alone.

> balance :: RBT a -> RBT a
> balance (N B (N R (N R a x b) y c) z d) = N R (N B a x b) y (N B c z d)
> balance (N B (N R a x (N R b y c)) z d) = N R (N B a x b) y (N B c z d)
> balance (N B a x (N R (N R b y c) z d)) = N R (N B a x b) y (N B c z d)
> balance (N B a x (N R b y (N R c z d))) = N R (N B a x b) y (N B c z d)
> balance t = t

Red-Black deletion
------------------

Deletion is more complicated [1].

> del :: Ord a => a -> RBT a -> RBT a
> del x E = E
> del x (N _ a y b)
>     | x < y     = delLeft  a y b
>     | x > y     = delRight a y b
>     | otherwise = merge a b
>  where
>    delLeft  a@(N B _ _ _) y b = balLeft (del x a) y b
>    delLeft  a             y b = N R (del x a) y b

>    delRight a y b@(N B _ _ _) = balRight a y (del x b)
>    delRight a y b             = N R a y (del x b)

The `del` function works by first finding the appropriate place in the tree to
delete the given element (if it exists).  At the node where we find the
element, we delete it by merging the two subtrees together.  At other nodes,
we call `del` recursively on one of the two subtrees, using `delLeft` and
`delRight`. If the subtree that we are deleting from is a black node, this
recursive call will change its black height, so we will need to rebalance to
restore the invariants (using `balLeft` and `balRight`).

In other words, we have an invariant that deleting an element from a *black*
tree of height `n + 1` returns a tree of height `n`, while deleting from a
*red* tree (or an empty tree) preserves the black height.

As above, the final tree that we produce may be red or black, so we blacken
this result to restore this invariant.

*Rebalancing function after a left deletion from a black-rooted tree*.  

There are three cases to consider:
  1. left subtree is red.
  2. both left and right subtrees are black.
  3. left subtree is black and right is red.

These three cases are covered by the following function. In each case, we
produce a balanced tree even though we know that the black height of the left
subtree is one less than the black height of the right subtree.

> balLeft :: RBT a -> a -> RBT a -> RBT a
> balLeft (N R a x b) y c            = N R (N B a x b) y c
> balLeft bl x (N B a y b)           = balance (N B bl x (N R a y b))
> balLeft bl x (N R (N B a y b) z c) =
>   N R (N B bl x a) y (balance (N B b z (redden c)))

Above, we need the following helper function to reduce the black height of the
subtree `c` reddening the node. This operation should only be called on black
nodes. Here, we know that `c` must be black because it is the child of a red
node, and we know that `c` can't be `E` because it must have the same black
height as `(N B a y b)`.

> redden :: RBT a -> RBT a
> redden (N B a x b) = N R a x b
> redden _ = error "invariant violation"

*Rebalance after deletion from the right subtree.* This function is symmetric
 to the above code.

> balRight :: RBT a -> a -> RBT a -> RBT a
> balRight a x (N R b y c)            = N R a x (N B b y c)
> balRight (N B a x b) y bl           = balance (N B (N R a x b) y bl)
> balRight (N R a x (N B b y c)) z bl =
>   N R (balance (N B (redden a) x b)) y (N B c z bl)

Finally, we need to glue two red-black trees together into a single tree
(after deleting the element in the middle). If one subtree is red and the
other black, we can call merge recursively, pushing the red node
up. Otherwise, if both subtrees are black or both red, we can merge the inner
pair of subtrees together. If that result is red, then we can promote its
value up. Otherwise, we may need to rebalance.

> merge :: RBT a -> RBT a -> RBT a
> merge E x = x
> merge x E = x
> merge (N R a x b) (N R c y d) =
>   case merge b c of
>     N R b' z c' -> N R (N R a x b') z (N R c' y d)
>     bc -> N R a x (N R bc y d)
> merge (N B a x b) (N B c y d) =
>   case merge b c of
>     N R b' z c' -> N R  (N B a x b') z (N B c' y d)
>     bc -> balLeft a x (N B bc y d)
> merge a (N R b x c)           = N R (merge a b) x c
> merge (N R a x b) c           = N R a x (merge b c)


We should use quickcheck to verify this definition. If you haven't already,
define some properties that will convince you that the deletion function above
is correct. 

> prop_delete_count ::  Int -> RBT Int -> Bool
> prop_delete_count x t = length (elements t) == length (elements (delete x t))
>   || length (elements t) == 1 + length (elements (delete x t))

> prop_delete_balance :: Int -> RBT Int -> Bool
> prop_delete_balance x t = elements (delete x t) == elements (delete x (delete x t))

Notes
-----

[0] See also persistant [Java
implementation](http://wiki.edinburghhacklab.com/PersistentRedBlackTreeSet)
for comparison. Requires ~350 lines for the same implementation.

[1] This implementation of deletion is taken from Stefan Kahrs, "Red-black
trees with types", Journal of functional programming, 11(04), pp 425-432, July
2001

[2] Andrew Appel, ["Efficient Verified Red-Black Trees"](http://www.cs.princeton.edu/~appel/papers/redblack.pdf) September
    2011. Presents a Coq implementation of a verified Red Black Tree based on
    Karhs implementation.

[3] Matt Might has a blog post on an alternative version of the [RBT deletion operation](http://matt.might.net/articles/red-black-delete/).

[4] (See also [this talk](https://www.youtube.com/watch?v=xcm_H36v_18) that
also develops an ordering check for binary trees.)
