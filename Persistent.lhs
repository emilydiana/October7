---
fulltitle: A Persistent Set Interface
date: October 7, 2019
---

Warning: we are going to use a few recent GHC extensions in this lecture.
We'll explain these extensions as we use them below.

> {-# LANGUAGE AllowAmbiguousTypes  #-}
> {-# LANGUAGE ScopedTypeVariables #-}
> {-# LANGUAGE TypeApplications #-}
> {-# LANGUAGE GeneralizedNewtypeDeriving #-} 
> 
> module Persistent where

> import Control.Monad
> import Test.QuickCheck hiding (elements)
> import Data.Maybe as Maybe
> import Data.List (sort,nub)

A persistent data structure is one where all of the operations are pure
functions.

For example, let's look at an interface of a simple *persistent* set of
ordered elements. We can tell that the implementation is persistent just by
looking at the types of the operations. In particular, the empty operation is
not a function, it is just a set --- there is only one empty set. If we were
allowed to mutate it, it wouldn't be empty any more.

> class Set s where
>    empty         :: s a
>    insert        :: Ord a => a -> s a -> s a
>    delete        :: Ord a => a -> s a -> s a 
>    member        :: Ord a => a -> s a -> Bool
>    elements      :: Ord a => s a -> [a]

We can tell that the *set* implementation is persistent just by looking at the
*types* of these operations. For example, the `insert` and `delete` operations
return a new set instead of modifying their argument.

Set Properties
--------------

What properties should instances of the `Set` interface satisfy? Can we test
those properties with QuickCheck?

When we define an abstract interface like `Set` above, using a type
class, we should also specify properties that *all* implementations should
satisfy.  What properties do you think a set should satisfy?

It should not have duplicate elements. If the set is not empty than the list of elements
should be non empty. It needs to contain all elements of the same type. If you insert an
element then you can delete it after. Sorted?

Below, we will define some of these properties as QuickCheck tests.

Here's an example property: The empty set has no elements.

> prop_empty :: forall s. (Set s) => Bool
> prop_empty = null (elements (empty :: s Int))

Although this property is simple to state, it is difficult to encode via
QuickCheck. The problem is that the type of this function is ambiguous --- the
type variable `s` only appears in the `Set` constraint and no where else in
the type. This is usually a bad situation, it means that type inference will
be unable to determine the type `s`. However, we will work around this
situation with GHC extensions. In particular, the extension
`AllowAmbiguousTypes` instructs GHC to permit types like the one above. To use
definitions with ambiguous types we also need to enable
`TypeApplications`. (Below, we will use a TypeApplication to tell GHC what `s`
should be.) 

The other tricky part of this definition is that, due to the ambiguity, we
need to add a type annotation to `empty`. Otherwise, GHC doesn't know what
empty set to use. However, we want our property to be generic, so we need a
yet another extension, called `ScopedTypeVariables` to bring the type variable
`s` into scope in the body of `prop_empty` using the keyword `forall`. That
way we can mention this type variable in the annotation `s Int`. Without this
`forall` the type variable `s` would be unbound.

We can also define properties for set insertion. Here are two potential ones:

> -- Anything inserted can be found in the set
> prop_insert :: Set s => Int -> s Int -> Bool
> prop_insert x y = member x (insert x y)

> -- We don't lose any set elements after an insertion.
> prop_insert_inequal :: Set s => Int -> Int -> s Int -> Property
> prop_insert_inequal x y s =
>     x /= y ==> member y s == member y (insert x s)

And here's one for `elements`:

> -- No duplicates in the elements
> prop_elements :: Set s => s Int -> Bool
> prop_elements s = length (nub l) == length l where
>                         l = elements s

These are only a few of the properties that a `Set` should satisfy. What else
can you think of?

Define at least one of your own set properties below (you'll probably need to
adjust the type annotation):

--> prop_myproperty x y = member x (insert x y)

--> prop_insert' :: set s => int -> s int -> bool
--> prop_insert' x y = member x (insert x y)

> prop_myproperty :: Set s => Int -> s Int -> Bool 
> prop_myproperty x s = (length (elements (insert x s)) == 
>    length (elements s)) || (length (elements (insert x s))) ==
>    (1 + length (elements s))

List implementation
-------------------

One trivial implementation of sets uses lists. Any list can represent a set;
though if we want a canonical representation of that set we will need to
remove duplicates and sort the list.

We'll create a newtype for this version so we don't confuse these lists with
regular lists. The `GeneralizedNewtypeDeriving` extension allows us to reuse
any class instance for lists as an instance for `ListSet`. This is useful for
`Arbitrary` --- we want to generate `ListSet`s in the same way as generating
lists.

One reason that we define this newtype is to *avoid* existing list instances
that we *don't want*. For example, we don't want to have the `Eq` or `Foldable`
instances around because they would leak the fact that we aren't ordering the
list or removing duplicates until we absolutely have to. 

> newtype ListSet a = ListSet [a] deriving (Show, Arbitrary)

> instance Set ListSet where
>    empty = ListSet []
>    insert x (ListSet xs) = ListSet (x:xs) 
>    member x (ListSet xs) = x `elem` xs
>    delete x (ListSet xs) = ListSet (filter (/= x) xs)
>    elements (ListSet xs) = sort (nub xs)

Let's make sure our implementation satisfies properties of sets.

> main :: IO ()
> main = do
>   quickCheck $ prop_empty @ListSet
>   quickCheck $ prop_elements @ListSet
>   quickCheck $ prop_insert @ListSet
>   quickCheck $ prop_insert_inequal @ListSet
>   quickCheck $ prop_myproperty @ListSet

Note that in each case we provide the list type constructor `ListSet` as a type
argument to the property. (Type arguments must begin with `@` in Haskell. We
can only supply them if the `TypeApplications` extension is enabled.)

    *Persistent> :set -XTypeApplications
    *Persistent> quickCheck $ prop_empty @ListSet


Persistent vs. Ephemeral
------------------------

* An *ephemeral* data structure is one for which only one version is
available at a time: after an update operation, the structure as it
existed before the update is lost.

For example, conventional arrays are ephemeral.  After a location in an array
is updated, its old contents are no longer available.

* A *persistent* structure is one where multiple version are
simultaneously accessible: after an update, both old and new versions
are available.

For example, a binary tree can be implemented persistently, so that after
insertion, the old value of the tree is still available.

Persistent data structures can sometimes be more expensive than their
ephemeral counterparts (in terms of constant factors and sometimes
also asymptotic complexity), but that cost is often insignificant
compared to their benefits:

   - better integration with concurrent programming (naturally lock-free)
   - simpler, more declarative implementations
   - better semantics for equality, hashing, etc.
   - access to *all* old versions (git for everything)

Next, we'll look at another persistent version of a common data structure:
Red-Black trees. These lectures demonstrate that functional programming is
adept at implementing sophisticated data structures. In particular, datatypes
and pattern matching make the implementation of persistent tree-like data
structures remarkably straightforward. These examples are drawn from Chris
Okasaki's excellent book [Purely Functional Data
Structures](http://www.amazon.com/Purely-Functional-Structures-Chris-Okasaki/dp/0521663504).

However, we'll only scratch the surface. There are many
industrial-strength persistent data structures out there.

  * Finger trees/Ropes, see  [Data.Sequence](http://www.haskell.org/ghc/docs/7.6.3/html/libraries/containers-0.5.0.0/Data-Sequence.html)
  * Size balanced trees, see [Data.Map](http://www.haskell.org/ghc/docs/7.6.3/html/libraries/containers-0.5.0.0/Data-Map.html)
  * Big-endian Patricia trees, see [Data.IntMap](http://www.haskell.org/ghc/docs/7.6.3/html/libraries/containers-0.5.0.0/Data-IntMap.html)
  * Hash array mapped tries, used in the [Clojure](http://en.wikipedia.org/wiki/Hash_array_mapped_trie) language
  * and [many more](http://cstheory.stackexchange.com/questions/1539/whats-new-in-purely-functional-data-structures-since-okasaki)
