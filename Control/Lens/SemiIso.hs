{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE FlexibleContexts #-}
{- |
Module      :  Control.Lens.SemiIso
Description :  Semi-isomorphisms.
Copyright   :  (c) Paweł Nowak
License     :  MIT

Maintainer  :  Paweł Nowak <pawel834@gmail.com>
Stability   :  experimental

Semi-isomorphisms were motivated by reversible parsing/pretty printing. For example
we can map a number 12 to a string "12" (and the other way around). But the isomorphism
is partial - we cannot map the string "forty-two" to a number.

Another example: when parsing a list of numbers like "12_53___42" we want to skip underscores
between numbers (and forget about them). During pretty printing we have to decide how many
underscores should we insert between numbers. Let's say we insert a single underscore. But now
@prettyPrint (parse "12_53___42") = "12_53_42"@ and not "12_53___42". We have to weaken
isomorphism laws to allow such semi-iso. Notice that

> parse (prettyPrint (parse "12_53___42"))       = parse "12_53___42"
> prettyPrint (parse (prettyPrint [12, 53, 42])) = prettyPrint [12, 53, 42]

Our semi-isomorphisms will obey weakened laws:

> apply i   >=> unapply i >=> apply i   = apply i
> unapply i >=> apply i   >=> unapply i = unapply i

When you see an "Either String a", the String is usually an error message.

Disclaimer: the name "semi-isomorphism" is fictitious and made up for this library.
Any resemblance to known mathematical objects of the same name is purely coincidental.
-}
module Control.Lens.SemiIso (
    -- * Semi-isomorphism types.
    SemiIso,
    SemiIso',
    ASemiIso,
    ASemiIso',

    -- * Patterns.
    pattern SemiIso,

    -- * Constructing semi-isos.
    semiIso,
    cloneSemiIso,

    -- * Reified semi-isos.
    ReifiedSemiIso'(..),
    reifySemiIso,

    -- * Consuming semi-isos.
    apply,
    unapply,
    withSemiIso,
    viewSemiIso,

    -- * Common semi-isomorphisms and isomorphisms.
    unit,
    swapped,
    associated,
    morphed,
    reorderMorphed,
    constant,
    exact,
    bifiltered,
    alwaysFailing,

    -- * Semi-isos for numbers.
    _Negative,

    -- * Transforming semi-isos.
    rev,
    prod,
    elimFirst,
    elimSecond,
    attempt,
    attemptAp,
    attemptUn,
    attempt_,
    attemptAp_,
    attemptUn_,

    -- * Bidirectional folds.
    bifoldr,
    bifoldr1,
    bifoldl,
    bifoldl1,

    bifoldr_,
    bifoldr1_,
    bifoldl_,
    bifoldl1_
    ) where

import Control.Arrow (Kleisli(..))
import Control.Category
import Control.Category.Structures
import Control.Lens.Internal.SemiIso
import Control.Lens.Iso
import Control.Tuple.Morph
import Data.Foldable
import Data.Functor.Identity
import Data.Profunctor.Exposed
import Data.Traversable
import Prelude hiding (id, (.))

-- | A semi-isomorphism is a partial isomorphism with weakened laws.
--
-- Should satisfy laws:
--
-- > apply i   >=> unapply i >=> apply i   = apply i
-- > unapply i >=> apply i   >=> unapply i = unapply i
--
-- Every 'Prism' is a 'SemiIso'.
-- Every 'Iso' is a 'Prism'.
type SemiIso s t a b = forall p f. (Exposed (Either String) p, Traversable f)
                     => p a (f b) -> p s (f t)

-- | Non-polymorphic variant of 'SemiIso'.
type SemiIso' s a = SemiIso s s a a

-- | When you see this as an argument to a function, it expects a 'SemiIso'.
type ASemiIso s t a b = Retail a b a (Identity b) -> Retail a b s (Identity t)

-- | When you see this as an argument to a function, it expects a 'SemiIso''.
type ASemiIso' s a = ASemiIso s s a a

-- | A nice pattern synonym for SemiIso's. Gives you the two functions, just like
-- 'viewSemiIso' or 'fromSemiIso'.
pattern SemiIso sa bt <- (viewSemiIso -> (sa, bt))

-- | A semi-iso stored in a container.
newtype ReifiedSemiIso' s a = ReifiedSemiIso' { runSemiIso :: SemiIso' s a }

instance Category ReifiedSemiIso' where
    id = ReifiedSemiIso' id
    ReifiedSemiIso' f . ReifiedSemiIso' g = ReifiedSemiIso' (g . f)

instance Products ReifiedSemiIso' where
    -- TODO: pattern synonyms dont work here for some reason
    first (ReifiedSemiIso' ai) = withSemiIso ai $ \f g ->
        ReifiedSemiIso' $ cloneSemiIso $
            semiIso (runKleisli $ first $ Kleisli f)
                    (runKleisli $ first $ Kleisli g)

    second (ReifiedSemiIso' ai) = withSemiIso ai $ \f g ->
        ReifiedSemiIso' $ cloneSemiIso $
            semiIso (runKleisli $ second $ Kleisli f)
                    (runKleisli $ second $ Kleisli g)

    ReifiedSemiIso' ai *** ReifiedSemiIso' ai' = ReifiedSemiIso' $
        withSemiIso ai $ \f g -> withSemiIso ai' $ \f' g' ->
            semiIso (runKleisli $ Kleisli f *** Kleisli f')
                    (runKleisli $ Kleisli g *** Kleisli g')

instance Coproducts ReifiedSemiIso' where
    left (ReifiedSemiIso' ai) = withSemiIso ai $ \f g ->
        ReifiedSemiIso' $ cloneSemiIso $
            semiIso (runKleisli $ left $ Kleisli f)
                    (runKleisli $ left $ Kleisli g)

    right (ReifiedSemiIso' ai) = withSemiIso ai $ \f g ->
        ReifiedSemiIso' $ cloneSemiIso $
            semiIso (runKleisli $ right $ Kleisli f)
                    (runKleisli $ right $ Kleisli g)

    ReifiedSemiIso' ai +++ ReifiedSemiIso' ai' = ReifiedSemiIso' $
        withSemiIso ai $ \f g -> withSemiIso ai' $ \f' g' ->
            semiIso (runKleisli $ Kleisli f +++ Kleisli f')
                    (runKleisli $ Kleisli g +++ Kleisli g')

instance CatPlus ReifiedSemiIso' where
    cempty = ReifiedSemiIso' $ alwaysFailing "cempty"

    ReifiedSemiIso' ai /+/ ReifiedSemiIso' ai' = ReifiedSemiIso' $
        withSemiIso ai $ \f g -> withSemiIso ai' $ \f' g' ->
            semiIso (runKleisli $ Kleisli f /+/ Kleisli f')
                    (runKleisli $ Kleisli g /+/ Kleisli g')

-- | Constructs a semi isomorphism from a pair of functions that can
-- fail with an error message.
semiIso :: (s -> Either String a) -> (b -> Either String t) -> SemiIso s t a b
semiIso sa bt = merge . dimap sa (sequenceA . fmap bt) . expose

-- | Clones a semi-iso.
cloneSemiIso :: ASemiIso s t a b -> SemiIso s t a b
cloneSemiIso (SemiIso sa bt) = semiIso sa bt

-- | Applies the 'SemiIso'.
apply :: ASemiIso s t a b -> s -> Either String a
apply (SemiIso sa _) = sa

-- | Applies the 'SemiIso' in the opposite direction.
unapply :: ASemiIso s t a b -> b -> Either String t
unapply (SemiIso _ bt) = bt

-- | Extracts the two functions that characterize the 'SemiIso'.
withSemiIso :: ASemiIso s t a b
            -> ((s -> Either String a) -> (b -> Either String t) -> r)
            -> r
withSemiIso ai k = case ai (Retail Right (Right . Identity)) of
                        Retail sa bt -> k sa (rmap (runIdentity . sequenceA) bt)

-- | Extracts the two functions that characterize the 'SemiIso'.
viewSemiIso :: ASemiIso s t a b -> (s -> Either String a, b -> Either String t)
viewSemiIso ai = withSemiIso ai (,)

-- | Reifies a semi-iso.
reifySemiIso :: ASemiIso' s a -> ReifiedSemiIso' s a
reifySemiIso ai = ReifiedSemiIso' $ cloneSemiIso ai

-- | A trivial isomorphism between a and (a, ()).
unit :: Iso' a (a, ())
unit = iso (, ()) fst

-- | Products are associative.
associated :: Iso' (a, (b, c)) ((a, b), c)
associated = iso (\(a, (b, c)) -> ((a, b), c)) (\((a, b), c) -> (a, (b, c)))

-- | An isomorphism between two arbitrary nested tuples, as long the contained
-- types (ignoring units!) read from left to right are the same.
--
-- This is implemented using 'Data.Tuple.Morph.morph' from 'tuple-morph'.
morphed :: (TupleMorphable a c, TupleMorphable b c)
        => Iso' a b
morphed = iso morphTuples morphTuples

-- | Like @morphed@ but also reorders elements if uniquely defined.
reorderMorphed
    :: (  TupleMorphable a b
        , TupleMorphable c d
        , ReorderList b d
        , ReorderList d b
        , CheckListsForTupleIso b d
        , CheckListsForTupleIso d b)
    => Iso' a c
reorderMorphed = iso morphReorderTuples morphReorderTuples

-- | \-> Always returns the argument.
--
-- \<- Maps everything to a @()@.
--
-- Note that this isn't an @Iso'@ because
--
-- > unapply (constant x) >=> apply (constant x) /= id
--
-- But SemiIso laws do hold.
constant :: a -> SemiIso' () a
constant x = semiIso (\_ -> Right x) (\_ -> Right ())

-- | \-> Filters out all values not equal to the argument.
--
-- \<- Always returns the argument.
exact :: Eq a => a -> SemiIso' a ()
exact x = semiIso f g
  where
    f y | x == y    = Right ()
        | otherwise = Left "exact: not equal"
    g _ = Right x

-- | Like 'filtered' but checks the predicate in both ways.
bifiltered :: (a -> Bool) -> SemiIso' a a
bifiltered p = semiIso check check
  where check x | p x       = Right x
                | otherwise = Left "bifiltered: predicate failed"

-- | A semi-iso that fails in both directions.
alwaysFailing :: String -> SemiIso s t a b
alwaysFailing msg = semiIso (\_ -> Left msg) (\_ -> Left msg)

-- | \-> Matches only negative numbers, turns it into a positive one.
--
-- \<- Matches only positive numbers, turns it into a negative one.
_Negative :: Real a => SemiIso' a a
_Negative = semiIso f g
  where
    f x | x < 0 = Right (-x)
        | otherwise = Left "_Negative: apply expected a negative number"
    g x | x >= 0 = Right (-x)
        | otherwise = Left "_Negative: unapply expected a positive number"

-- | Reverses a 'SemiIso'.
rev :: ASemiIso s t a b -> SemiIso b a t s
rev ai = withSemiIso ai $ \l r -> semiIso r l

-- | A product of semi-isos.
prod :: ASemiIso' s a -> ASemiIso' t b -> SemiIso' (s, t) (a, b)
prod a b = runSemiIso (reifySemiIso a *** reifySemiIso b)

-- | Uses an @SemiIso' a ()@ to construct a @SemiIso' (a, b) b@,
-- i.e. eliminates the first pair element.
elimFirst :: ASemiIso' s () -> SemiIso' (s, t) t
elimFirst ai = swapped . elimSecond ai

-- | Uses an @SemiIso b ()@ to construct a @SemiIso (a, b) a@,
-- i.e. eliminates the second pair element.
elimSecond :: ASemiIso' s () -> SemiIso' (t, s) t
elimSecond ai = runSemiIso (id *** reifySemiIso ai) . rev unit

-- | Transforms the semi-iso so that applying it in both directions never fails,
-- but instead catches any errors and returns them as an @Either String a@.
attempt :: ASemiIso s t a b -> SemiIso s (Either String t) (Either String a) b
attempt = attemptAp . attemptUn

-- | Transforms the semi-iso so that applying it in direction (->) never fails,
-- but instead catches any errors and returns them as an @Either String a@.
attemptAp :: ASemiIso s t a b -> SemiIso s t (Either String a) b
attemptAp (SemiIso sa bt) = semiIso (Right . sa) bt

-- | Transforms the semi-iso so that applying it in direction (<-) never fails,
-- but instead catches any errors and returns them as an @Either String a@.
attemptUn :: ASemiIso s t a b -> SemiIso s (Either String t) a b
attemptUn (SemiIso sa bt) = semiIso sa (Right . bt)

discard :: Either a b -> Maybe b
discard = either (const Nothing) Just

-- | Transforms the semi-iso like 'attempt', but ignores the error message.
attempt_ :: ASemiIso s t a b -> SemiIso s (Maybe t) (Maybe a) b
attempt_ ai = rmap (fmap discard) . attempt ai . lmap discard

-- | Transforms the semi-iso like 'attemptAp', but ignores the error message.
--
-- Very useful when you want to bifold using a prism.
attemptAp_ :: ASemiIso s t a b -> SemiIso s t (Maybe a) b
attemptAp_ ai = attemptAp ai . lmap discard

-- | Transforms the semi-iso like 'attemptUn', but ignores the error message.
attemptUn_ :: ASemiIso s t a b -> SemiIso s (Maybe t) a b
attemptUn_ ai = rmap (fmap discard) . attemptUn ai

-- | Monadic counterpart of 'foldl1' (or non-empty list counterpart of 'foldlM').
foldlM1 :: Monad m => (a -> a -> m a) -> [a] -> m a
foldlM1 f (x:xs) = foldlM f x xs
foldlM1 _ []     = fail "foldlM1: empty list"

-- | Monadic counterpart of 'foldr1' (or non-empty list counterpart of 'foldrM').
foldrM1 :: Monad m => (a -> a -> m a) -> [a] -> m a
foldrM1 _ [x]    = return x
foldrM1 f (x:xs) = foldrM1 f xs >>= f x
foldrM1 _ []     = fail "foldrM1: empty list"

-- | Monadic counterpart of 'unfoldr'.
unfoldrM :: Monad m => (a -> m (Maybe (b, a))) -> a -> m (a, [b])
unfoldrM f a = do
    r <- f a
    case r of
      Just (b, new_a) -> do
          (final_a, bs) <- unfoldrM f new_a
          return (final_a, b : bs)
      Nothing -> return (a, [])

-- | A variant of 'unfoldrM' that always produces a non-empty list.
unfoldrM1 :: Monad m => (a -> m (Maybe (a, a))) -> a -> m [a]
unfoldrM1 f a = do
    r <- f a
    case r of
      Just (b, new_a) -> do
          bs <- unfoldrM1 f new_a
          return (b : bs)
      Nothing -> return [a]

-- | Monadic counterpart of 'unfoldl'.
unfoldlM :: Monad m => (a -> m (Maybe (a, b))) -> a -> m (a, [b])
unfoldlM f a0 = go a0 []
  where
    go a bs = do
        r <- f a
        case r of
          Just (new_a, b) -> go new_a (b : bs)
          Nothing -> return (a, bs)

-- | A variant of 'unfoldlM' that always produces a non-empty list.
unfoldlM1 :: Monad m => (a -> m (Maybe (a, a))) -> a -> m [a]
unfoldlM1 f a0 = go a0 []
  where
    go a bs = do
        r <- f a
        case r of
          Just (new_a, b) -> go new_a (b : bs)
          Nothing -> return (a : bs)

-- | Constructs a bidirectional fold. Works with prisms.
--
-- \-> Right unfolds using the (->) part of the given semi-iso, until it fails.
--
-- \<- Right folds using the (<-) part of the given semi-iso.
bifoldr :: ASemiIso' a (b, a) -> SemiIso' a (a, [b])
bifoldr = bifoldr_ . attemptAp_

-- | Constructs a bidirectional fold. Works with prisms.
--
-- \-> Right unfolds using the (->) part of the given semi-iso, until it fails.
-- It should produce a non-empty list.
--
-- \<- Right folds a non-empty list using the (<-) part of the given semi-iso.
bifoldr1 :: ASemiIso' a (a, a) -> SemiIso' a [a]
bifoldr1 = bifoldr1_ . attemptAp_

-- | Constructs a bidirectional fold. Works with prisms.
--
-- \-> Left unfolds using the (->) part of the given semi-iso, until it fails.
--
-- \<- Left folds using the (<-) part of the given semi-iso.
bifoldl :: ASemiIso' a (a, b) -> SemiIso' a (a, [b])
bifoldl = bifoldl_ . attemptAp_

-- | Constructs a bidirectional fold. Works with prisms.
--
-- \-> Left unfolds using the (->) part of the given semi-iso, until it fails.
-- It should produce a non-empty list.
--
-- \<- Left folds a non-empty list using the (<-) part of the given semi-iso.
bifoldl1 :: ASemiIso' a (a, a) -> SemiIso' a [a]
bifoldl1 = bifoldl1_ . attemptAp_

-- | Constructs a bidirectional fold.
--
-- \-> Right unfolds using the (->) part of the given semi-iso.
--
-- \<- Right folds using the (<-) part of the given semi-iso.
bifoldr_ :: ASemiIso a a (Maybe (b, a)) (b, a) -> SemiIso' a (a, [b])
bifoldr_ ai = semiIso (uf ai) (f ai)
  where
    f = uncurry . foldrM . curry . unapply
    uf = unfoldrM . apply

-- | Constructs a bidirectional fold.
--
-- \-> Right unfolds using the (->) part of the given semi-iso. It should
-- produce a non-empty list.
--
-- \<- Right folds a non-empty list using the (<-) part of the given semi-iso.
bifoldr1_ :: ASemiIso a a (Maybe (a, a)) (a, a) -> SemiIso' a [a]
bifoldr1_ ai = semiIso (uf ai) (f ai)
  where
    f = foldrM1 . curry . unapply
    uf = unfoldrM1 . apply

-- | Constructs a bidirectional fold.
--
-- \-> Left unfolds using the (->) part of the given semi-iso.
--
-- \<- Left folds using the (<-) part of the given semi-iso.
bifoldl_ :: ASemiIso a a (Maybe (a, b)) (a, b) -> SemiIso' a (a, [b])
bifoldl_ ai = semiIso (uf ai) (f ai)
  where
    f = uncurry . foldlM . curry . unapply
    uf = unfoldlM . apply

-- | Constructs a bidirectional fold.
--
-- \-> Left unfolds using the (->) part of the given semi-iso. It should
-- produce a non-empty list.
--
-- \<- Left folds a non-empty list using the (<-) part of the given semi-iso.
bifoldl1_ :: ASemiIso a a (Maybe (a, a)) (a, a) -> SemiIso' a [a]
bifoldl1_ ai = semiIso (uf ai) (f ai)
  where
    f = foldlM1 . curry . unapply
    uf = unfoldlM1 . apply
