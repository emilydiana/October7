---
fulltitle: "In class exercise: QuickCheck properties for lists"
date: October 2, 2019
---

> {-# OPTIONS -Wincomplete-patterns #-}
> {-# LANGUAGE FlexibleInstances, FlexibleContexts #-}

> module QuickList where

> import Test.QuickCheck
> import System.Random (Random)

> import Data.List as List
> import Control.Monad (liftM, liftM2)

In this problem, you'll be writing QuickCheck properties to specify
various list manipulation functions.  For each property that you write, you
should also include a buggy implementation of the tested function that
_does not_ satisfy the property you wrote.  We'll be asking you to
write your properties in a very particular way.  For instance, suppose
you are testing the
[`const`](http://hackage.haskell.org/package/base-4.6.0.1/docs/Prelude.html#v:const)
function, which takes two arguments and returns the first one.  Here's
how you'd normally test (a type-restricted version of) it.  First, we
write an appropriate property:

> prop_const' :: Eq a => a -> a -> Bool
> prop_const' a b = const a b == a

Then we see what QuickCheck thinks of the property by entering this in GHCi:

       *Main> quickCheck (prop_const :: Char -> Char -> Bool)

(The type annotation is needed because `prop_const` is polymorphic;
QuickCheck wouldn't know what type of test data to generate if we left
it off.)

Below, we'll be asking you to fill in most of the definition and the type
signature, given code snippets such as

~~~~{.haskell}
prop_const :: (a -> a -> a) -> Undefined
prop_const const' = undefined
~~~~

where `Undefined` is a dummy Testable type that will emit an error
if used:

> data Undefined
> instance Testable Undefined where
>   property = error "Unimplemented property"

Filling in the property will then involve

  * Adding parameters,
  * Replacing the body, and
  * Replacing the `Undefined` type with the desired type of the property.

That will look, for instance, like so:

> prop_const :: Eq a => (a -> a -> a) -> a -> a -> Bool
> prop_const const' a b = const' a b == a

You'll fill in the types of all the parameters plus the return type,
and you can add any type class constraints you want.

Notice that this property has an extra parameter `const'`.  When you
write your tests this way, and use the passed in parameter (here
`const'`) instead of the real function (here `const`), you will be
able to test your buggy implementations as well.  For instance,
suppose that you have:

> constBug :: a -> a -> a
> constBug _ b = b -- Oops: this returns the *second* argument, not the first.

Then you'll be able to test your property on both `const` (where it will pass)
and `constBug` (where it will not):

    *Main> quickCheck (prop_const const :: Char -> Char -> Bool)
    +++ OK, passed 100 tests.
    *Main> quickCheck (prop_const constBug :: Char -> Char -> Bool)
    *** Failed! Falsifiable (after 1 test and 2 shrinks):
    'a'
    'b'


-- Part a

Define a property showing that
[`minimum`](http://hackage.haskell.org/package/base-4.6.0.1/docs/Prelude.html#v:minimum)
really returns the smallest element in a list; also, write a buggy
implementation of `minimum` that doesn't satisfy your property.
(Don't forget to fill in the type signature for `prop_minimum`!)

> prop_minimum1 :: Ord a => ([a] -> a) -> [a] -> [a] -> Property
> prop_minimum1 minimum' l1 l2 =
>   not (null l1) ==> not (null l2) ==>
>   minimum' (l1 ++ l2) == min (minimum' l1) (minimum' l2)

> prop_minimum2 :: Ord a => ([a] -> a) -> [a] -> Bool
> prop_minimum2 minimum' l1 = 
>    (null l1) || minimum' l1 == head (sort l1)

> prop_minimum3 :: Ord a => ([a] -> a) -> [a] -> Property
> prop_minimum3 minimum' l1 =
>    not (null l1) ==> minimum' l1 == List.minimum l1

> prop_minimum :: Ord a => ([a] -> a) -> [a] -> Property 
> prop_minimum minimum' l = not (null l) ==>  minimum' l == head (sort l)

> minimumBug :: Ord a => [a] -> a
> minimumBug = head 



-- Part b

Define a property specifying the
[`replicate`](http://hackage.haskell.org/package/base-4.6.0.1/docs/Prelude.html#v:replicate)
function from the standard library, and a buggy implementation that
violates this spec.  Recall that `replicate k x` is a list containing
`k` copies of `x`.  One QuickCheck feature that will be important here
(and later) is the use of `newtype`s, such as
[`NonNegative`](http://hackage.haskell.org/package/QuickCheck-2.6/docs/Test-QuickCheck-Modifiers.html#t:NonNegative),
to restrict the domain of arbitrarily generated values:

    Prelude Test.QuickCheck> sample (arbitrary :: Gen Int)
    1
    -2
    4
    -7
    -9
    -20
    -1
    22
    60
    -1780
    3770
    Prelude Test.QuickCheck> sample (arbitrary :: Gen NonNegative Int)
    NonNegative {getNonNegative = 1}
    NonNegative {getNonNegative = 0}
    NonNegative {getNonNegative = 1}
    NonNegative {getNonNegative = 8}
    NonNegative {getNonNegative = 32}
    NonNegative {getNonNegative = 5}
    NonNegative {getNonNegative = 28}
    NonNegative {getNonNegative = 23}
    NonNegative {getNonNegative = 662}
    NonNegative {getNonNegative = 584}
    NonNegative {getNonNegative = 0}


However, simply using `NonNegative Int` won't work here, as
generating, say, a million-element list will take far too long (try
it!).

So, your job is to define a `newtype` for generating *small*
non-negative integers (say, in the range 0 to 1000):


> newtype SmallNonNegInt = SmallNonNegInt Int deriving (Eq, Ord, Show, Read)

When you make a quickcheck instance, you should define both `arbitrary` and
`shrink` for the `SmallNonNegInt` type. Note: the shrink function in this instance can
be derived from shrinking the int inside.  Try it out first:

     Prelude Test.QuickCheck> shrink (10 :: Int)
     [0,5,8,9]

> instance Arbitrary SmallNonNegInt where
>     arbitrary = elements (map SmallNonNegInt [0 .. 1000])
>     shrink (SmallNonNegInt n) = fmap SmallNonNegInt (shrink n)  

Then, use this type to define your property specifying `replicate`.

> prop_replicate :: (Int -> a -> [a]) -> Undefined
> prop_replicate = undefined

--> prop_replicate replicate' (SmallNonNegInt n) x = replicate' n x == fmap SmallNonNegInt   

> replicateBug :: Int -> a -> [a]
> replicateBug = undefined



-- Part c

Define two properties specifying
[`group`](http://hackage.haskell.org/package/base-4.6.0.1/docs/Data-List.html#v:group);
the first one should say that "the concatenation of the result is
equal to the argument", and the second should say that "each sublist
in the result is non-empty and contains only equal elements".  Also
write a buggy version of `group` that violates both of them.

> prop_group_1 :: Eq a => ([a] -> [[a]]) -> Undefined
> prop_group_1 group' = undefined

> prop_group_2 :: Eq a => ([a] -> [[a]]) -> Undefined
> prop_group_2 group' = undefined

> groupBug :: Eq a => [a] -> [[a]]
> groupBug = undefined



-- Part d

Write two interesting properties about
[`reverse`](http://hackage.haskell.org/package/base-4.6.0.1/docs/Prelude.html#v:reverse).
Write two different buggy versions, one which violates each property.

> prop_reverse_1 :: ([a] -> [a]) -> Undefined
> prop_reverse_1 reverse' = undefined

> prop_reverse_2 :: ([a] -> [a]) -> Undefined
> prop_reverse_2 reverse' = undefined
> 
> reverseBug_1 :: [a] -> [a]
> reverseBug_1 = undefined

> reverseBug_2 :: [a] -> [a]
> reverseBug_2 = undefined



Once you've written all of these, evaluating `main` in GHCi should
produce the expected output:

> main :: IO ()
> main = do
>   let qcName name prop = do
>         putStr $ name ++ ": "
>         quickCheck prop

>   putStrLn "The following tests should all succeed:"
>   qcName "const"     $ prop_const     (const     :: Char -> Char -> Char)
>   qcName "minimum"   $ prop_minimum   (minimum   :: String -> Char)
>   qcName "replicate" $ prop_replicate (replicate :: Int -> Char -> String)
>   qcName "group_1"   $ prop_group_1   (group     :: String -> [String])
>   qcName "group_2"   $ prop_group_2   (group     :: String -> [String])
>   qcName "reverse_1" $ prop_reverse_1 (reverse   :: String -> String)
>   qcName "reverse_2" $ prop_reverse_2 (reverse   :: String -> String)

>   putStrLn ""

>   putStrLn "The following tests should all fail:"
>   qcName "const"     $ prop_const     (constBug     :: Char -> Char -> Char)
>   qcName "minimum"   $ prop_minimum   (minimumBug   :: String -> Char)
>   qcName "replicate" $ prop_replicate (replicateBug :: Int -> Char -> String)
>   qcName "group_1"   $ prop_group_1   (groupBug     :: String -> [String])
>   qcName "group_2"   $ prop_group_2   (groupBug     :: String -> [String])
>   qcName "reverse_1" $ prop_reverse_1 (reverseBug_1 :: String -> String)
>   qcName "reverse_2" $ prop_reverse_2 (reverseBug_2 :: String -> String)
