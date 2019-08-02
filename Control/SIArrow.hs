{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{- |
Module      :  Control.SIArrow
Description :  Categories of reversible computations.
Copyright   :  (c) Paweł Nowak
License     :  MIT

Maintainer  :  Paweł Nowak <pawel834@gmail.com>
Stability   :  experimental

Categories of reversible computations.
-}
module Control.SIArrow (
    -- * Arrow.
    SIArrow(..),
    (^>>), (>>^), (^<<), (<<^),
    (#>>), (>>#), (#<<), (<<#),

    -- * Functor and applicative.
    (/$/), (/*/), (/*), (*/),

    -- * Signaling errors.
    sifail, (/?/),

    -- * Combinators.
    sisequence,
    sisequence_,
    sireplicate,
    sireplicate_
    ) where

import Control.Arrow (Kleisli(..))
import Control.Category
import Control.Category.Structures
import Control.Lens.Cons
import Control.Lens.Empty
import Control.Lens.Iso
import Control.Lens.SemiIso
import Control.Monad
import Data.Semigroupoid.Dual
import Prelude hiding (id, (.))

infixr 1 ^>>, ^<<, #>>, #<<
infixl 1 >>^, <<^, >>#, <<#
infixl 4 /$/
infixl 5 /*/, */, /*
infixl 3 /?/

-- | A category equipped with an embedding 'siarr' from @SemiIso@ into @cat@ and some
-- additional structure.
--
-- SIArrow abstracts categories of reversible computations
-- (with reversible side effects).
--
-- The category @cat@ should contain @SemiIso@ as a sort of
-- \"subcategory of pure computations\".
class (Products cat, Coproducts cat, CatPlus cat) => SIArrow cat where
    -- | Allows you to lift a SemiIso into @cat@. The resulting arrow should be
    -- in some sense minimal or \"pure\", similiar to 'pure', 'return' and
    -- 'arr' from "Control.Category".
    siarr :: ASemiIso' a b -> cat a b
    siarr = sipure . rev

    -- | Reversed version of 'siarr'.
    --
    -- Use this where you would use 'pure'.
    sipure :: ASemiIso' b a -> cat a b
    sipure = siarr . rev

    -- | Allows a computation to depend on a its input value.
    --
    -- I am not sure if this is the right way to get that ArrowApply or Monad
    -- like power. It seems quite easy to break the parser/pretty-printer inverse
    -- guarantee using this. On the other hand we have to be careful only when
    -- constructing the SemiIso using 'iso'/'semiIso' - and with an invalid SemiIso
    -- we could break everything anyway using 'siarr'.
    sibind :: ASemiIso a (cat a b) (cat a b) b -> cat a b

    -- | @sisome v@ repeats @v@ as long as possible, but no less then once.
    sisome :: cat () b -> cat () [b]
    sisome v = _Cons /$/ v /*/ simany v

    -- | @simany v@ repeats @v@ as long as possible.
    simany :: cat () b -> cat () [b]
    simany v = sisome v /+/ sipure _Empty

    {-# MINIMAL (siarr | sipure), sibind #-}

instance MonadPlus m => SIArrow (Kleisli m) where
    siarr ai = Kleisli $ either fail return . apply ai
    sibind ai = Kleisli $ \a -> either fail (($ a) . runKleisli) $ apply ai a

instance SIArrow cat => SIArrow (Dual cat) where
    siarr = Dual . sipure
    sibind ai = Dual $ sibind (iso id getDual . rev ai . iso getDual id)

instance SIArrow ReifiedSemiIso' where
    siarr = reifySemiIso
    sibind ai = ReifiedSemiIso' $
        semiIso (\a -> apply ai a >>= flip apply a . runSemiIso)
                (\b -> unapply ai b >>= flip unapply b . runSemiIso)

-- | Composes a SemiIso with an arrow.
(^>>) :: SIArrow cat => ASemiIso' a b -> cat b c -> cat a c
f ^>> a = a . siarr f

-- | Composes an arrow with a SemiIso.
(>>^) :: SIArrow cat => cat a b -> ASemiIso' b c -> cat a c
a >>^ f = siarr f . a

-- | Composes a SemiIso with an arrow, backwards.
(^<<) :: SIArrow cat => ASemiIso' b c -> cat a b -> cat a c
f ^<< a = siarr f . a

-- | Composes an arrow with a SemiIso, backwards.
(<<^) :: SIArrow cat => cat b c -> ASemiIso' a b -> cat a c
a <<^ f = a . siarr f

-- | Composes a reversed SemiIso with an arrow.
(#>>) :: SIArrow cat => ASemiIso' b a -> cat b c -> cat a c
f #>> a = a . sipure f

-- | Composes an arrow with a reversed SemiIso.
(>>#) :: SIArrow cat => cat a b -> ASemiIso' c b -> cat a c
a >># f = sipure f . a

-- | Composes a reversed SemiIso with an arrow, backwards.
(#<<) :: SIArrow cat => ASemiIso' c b -> cat a b -> cat a c
f #<< a = sipure f . a

-- | Composes an arrow with a reversed SemiIso, backwards.
(<<#) :: SIArrow cat => cat b c -> ASemiIso' b a -> cat a c
a <<# f = a . sipure f

-- | Postcomposes an arrow with a reversed SemiIso.
-- The analogue of '<$>' and synonym for '#<<'.
(/$/) :: SIArrow cat => ASemiIso' b' b -> cat a b -> cat a b'
(/$/) = (#<<)

-- | The product of two arrows with duplicate units removed. Side effect are
-- sequenced from left to right.
--
-- The uncurried analogue of '<*>'.
(/*/) :: SIArrow cat => cat () b -> cat () c -> cat () (b, c)
a /*/ b = unit ^>> (a *** b)

-- | The product of two arrows, where the second one has no input and no output
-- (but can have side effects), with duplicate units removed. Side effect are
-- sequenced from left to right.
--
-- The uncurried analogue of '<*'.
(/*)  :: SIArrow cat => cat () a -> cat () () -> cat () a
f /* g = unit /$/ f /*/ g

-- | The product of two arrows, where the first one has no input and no output
-- (but can have side effects), with duplicate units removed. Side effect are
-- sequenced from left to right.
--
-- The uncurried analogue of '*>'.
(*/)  :: SIArrow cat => cat () () -> cat () a -> cat () a
f */ g = unit . swapped /$/ f /*/ g

-- | An arrow that fails with an error message.
sifail :: SIArrow cat => String -> cat a b
sifail = siarr . alwaysFailing

-- | Provides an error message in the case of failure.
(/?/) :: SIArrow cat => cat a b -> String -> cat a b
f /?/ msg = f /+/ sifail msg

-- | Equivalent of 'sequence'.
sisequence :: SIArrow cat => [cat () a] -> cat () [a]
sisequence [] = sipure _Empty
sisequence (x:xs) = _Cons /$/ x /*/ sisequence xs

-- | Equivalent of 'sequence_', restricted to units.
sisequence_ :: SIArrow cat => [cat () ()] -> cat () ()
sisequence_ [] = sipure _Empty
sisequence_ (x:xs) = unit /$/ x /*/ sisequence_ xs

-- | Equivalent of 'replicateM'.
sireplicate :: SIArrow cat => Int -> cat () a -> cat () [a]
sireplicate n f = sisequence (replicate n f)

-- | Equivalent of 'replicateM_', restricted to units.
sireplicate_ :: SIArrow cat => Int -> cat () () -> cat () ()
sireplicate_ n f = sisequence_ (replicate n f)
