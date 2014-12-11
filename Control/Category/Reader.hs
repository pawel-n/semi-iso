{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{- |
Module      :  Control.Category.Reader
Description :  Reader category transformer.
Copyright   :  (c) Paweł Nowak
License     :  MIT

Maintainer  :  Paweł Nowak <pawel834@gmail.com>
Stability   :  experimental

Provides a Reader category transformer.
-}
module Control.Category.Reader (
    ReaderCT(..)
    ) where

import Control.Category
import Control.SIArrow
import Prelude hiding (id, (.))

newtype ReaderCT env cat a b = ReaderCT { runReaderCT :: env -> cat a b }

instance CategoryTrans (ReaderCT env) where
    clift = ReaderCT . const

instance Category cat => Category (ReaderCT env cat) where
    id = clift id
    ReaderCT f . ReaderCT g = ReaderCT $ \x -> f x . g x

instance Products cat => Products (ReaderCT env cat) where
    ReaderCT f *** ReaderCT g = ReaderCT $ \x -> f x *** g x

instance Coproducts cat => Coproducts (ReaderCT env cat) where
    ReaderCT f +++ ReaderCT g = ReaderCT $ \x -> f x +++ g x

instance CategoryPlus cat => CategoryPlus (ReaderCT env cat) where
    cempty = clift cempty
    ReaderCT f /+/ ReaderCT g = ReaderCT $ \x -> f x /+/ g x

instance SIArrow cat => SIArrow (ReaderCT env cat) where
    siarr = clift . siarr