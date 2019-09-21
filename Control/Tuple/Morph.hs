{-# LANGUAGE
    PolyKinds,
    DataKinds,
    TypeOperators,
    GADTs,
    FunctionalDependencies,
    TypeFamilies,
    FlexibleInstances,
    UndecidableInstances,
    PatternSynonyms,
    RankNTypes,
    AllowAmbiguousTypes,
    TypeApplications,
    ScopedTypeVariables,
    ConstraintKinds,
    FlexibleContexts
    #-}

{-# OPTIONS_GHC -Wno-incomplete-patterns #-}

module Control.Tuple.Morph
    ( morphTuples
    , morphReorderTuples
    , morphPickTuples
    , TupleMorphable
    , CheckListsForTupleIso
    , ReorderList
    ) where

import Data.Proxy
import GHC.Generics
import GHC.TypeLits hiding (Nat)
import Data.Kind


morphTuples :: (TupleMorphable a c, TupleMorphable b c) => a -> b
morphTuples = morph . unmorph

morphPickTuples
    ::  ( TupleMorphable a b
        , TupleMorphable c d
        , ReorderList b d )
    => a
    -> c
morphPickTuples = morph . hReorder Proxy . unmorph

type CheckListsForTupleIso b d
    = EqOrError (Length b) (Length d)
        ('Text "Not isomorphic tuple contents:"
            ':$$: 'Text "    " ':<>: 'ShowType b
            ':$$: 'Text "    " ':<>: 'ShowType d)

morphReorderTuples
    ::  ( TupleMorphable a b
        , TupleMorphable c d
        , ReorderList b d
        , CheckListsForTupleIso b d)
    => a
    -> c
morphReorderTuples = morph . hReorder Proxy . unmorph

type family EqOrError a b e :: Constraint where
    EqOrError a a _ = a ~ a
    EqOrError _ _ e = TypeError e


-- # Nat

data Nat where
    S :: Nat -> Nat
    Z :: Nat


-- # HList

data HList (ts :: [*]) where
    HCons :: t -> HList tt -> HList (t ': tt)
    HNil :: HList '[]

infixr 5 :+
pattern (:+) :: (ts ~ (t : tt)) => t -> HList tt -> HList ts
pattern (:+) a b = HCons a b

-- ## Taking

class TakeableList (n :: Nat) aa bb | n aa -> bb where
    hTake :: Proxy n -> HList aa -> HList bb

instance TakeableList 'Z a '[] where
    hTake _ _ = HNil

instance (TakeableList n aa bb', bb ~ (a ': bb'))
    => TakeableList ('S n) (a ': aa) bb where
    hTake (Proxy :: Proxy ('S n)) (a :+ aa) = a :+ hTake @n Proxy aa

-- ## Dropping

class DroppableList (n :: Nat) (aa :: [*]) (bb :: [*]) | n aa -> bb where
    hDrop :: Proxy n -> HList aa -> HList bb

instance DroppableList 'Z aa aa where
    hDrop _ aa = aa

instance (DroppableList n aa bb) => DroppableList ('S n) (a ': aa) bb where
    hDrop (Proxy :: Proxy ('S n)) (_ :+ aa) = hDrop @n Proxy aa

-- ## Appending

infixr 4 ++:
class AppendableList aa bb cc | aa bb -> cc where
    (++:) :: HList aa -> HList bb -> HList (aa ++ bb)

instance AppendableList '[] bb bb where
    HNil ++: bb = bb

instance
    ( AppendableList aa bb cc
    , cc ~ (aa ++ bb)
    , ((a ': aa) ++ bb) ~ (a ': cc))
    => AppendableList (a ': aa) bb (a ': cc) where
    (a :+ aa) ++: bb = a :+ (aa ++: bb)

-- ## Finding

class FindableList ts t where
    hFind :: HList ts -> t

instance {-# OVERLAPPING #-}
    (NotFindableList ts t)
    => FindableList (t ': ts) t where
    hFind (t :+ _) = t

instance
    (TEq a t ~ 'False, FindableList ts a)
    => FindableList (t ': ts) a where
    hFind (_ :+ ts) = hFind ts

instance
    (TypeError
        ('Text "Could not find type " ':<>: 'ShowType a ':<>: 'Text " in tuple."))
    => FindableList '[] a where
    hFind = error "oh no"

class NotFindableList ts t

instance {-# OVERLAPPING #-}
    (TypeError
        ('Text "Type " ':<>: 'ShowType t ':<>: 'Text " is not unique in tuple."))
    => NotFindableList (t ': ts) t

instance (NotFindableList ts a) => NotFindableList (t ': ts) a

instance NotFindableList '[] a

class ReorderList as bs where
    hReorder :: Proxy bs -> HList as -> HList bs

instance (FindableList as b, ReorderList as bs) => ReorderList as (b ': bs) where
    hReorder _ as = hFind as :+ hReorder (Proxy @bs) as

instance ReorderList as '[] where
    hReorder _ _ = HNil

type family TEq a b :: Bool where
    TEq a a = 'True
    TEq a b = 'False

-- ## Other

type family (++) (as :: [k]) (bs :: [k]) :: [k] where
  (++) a '[] = a
  (++) '[] b = b
  (++) (a ': as) bs = a ': (as ++ bs)

type family Length (aa :: [k]) :: Nat where
    Length '[] = 'Z
    Length (a ': aa) = 'S (Length aa)


-- # Morphing

class TupleMorphable t th | t -> th where
    unmorph :: t -> HList th
    morph :: HList th -> t

instance (IsMophableTuple t ~ flag, TupleMorphable' t th flag) => TupleMorphable t th where
    unmorph = unmorph' (Proxy @flag)
    morph = morph' (Proxy @flag)

-- ## Implementation

class TupleMorphable' t th (flag :: Bool) | t flag -> th where
    unmorph' :: Proxy flag -> t -> HList th
    morph' :: Proxy flag -> HList th -> t

instance TupleMorphable' t '[t] 'False where
    unmorph' _ t = t :+ HNil
    morph' _ (t :+ HNil) = t

instance (GenericTupleMorphable (Rep t) th, Generic t) => TupleMorphable' t th 'True where
    unmorph' _ = genericUnmorph . from
    morph' _ = to . genericMorph

-- ### Generics

class GenericTupleMorphable f th | f -> th where
    genericUnmorph :: f p -> HList th
    genericMorph :: HList th -> f p

instance (GenericTupleMorphable f t) => GenericTupleMorphable (M1 i c f) t where
    genericUnmorph = genericUnmorph . unM1
    genericMorph = M1 . genericMorph

instance (TupleMorphable c t) => GenericTupleMorphable (K1 i c) t where
    genericUnmorph = unmorph . unK1
    genericMorph = K1 . morph

instance GenericTupleMorphable U1 '[] where
    genericUnmorph _ = HNil
    genericMorph _ = U1

type CanTakeDrop a b c =
    ( TakeableList (Length a) c a
    , DroppableList (Length a) c b
    , c ~ (a ++ b)
    )

instance
    ( GenericTupleMorphable f a
    , GenericTupleMorphable g b
    , AppendableList a b c
    , CanTakeDrop a b c)
    => GenericTupleMorphable (f :*: g) c where
    genericUnmorph (a :*: b) = genericUnmorph a ++: genericUnmorph b
    genericMorph cc = genericMorph aa :*: genericMorph bb
        where
            aa = hTake @(Length a) Proxy cc
            bb = hDrop @(Length a) Proxy cc

-- ## Other

type family (IsMophableTuple t) :: Bool where
    IsMophableTuple () = 'True
    IsMophableTuple (a, b) = 'True
    IsMophableTuple (a, b, c) = 'True
    IsMophableTuple (a, b, c, d) = 'True
    IsMophableTuple (a, b, c, d, e) = 'True
    IsMophableTuple (a, b, c, d, e, f) = 'True
    IsMophableTuple (a, b, c, d, e, f, g) = 'True
    IsMophableTuple (a, b, c, d, e, f, g, h) = 'True
    IsMophableTuple (a, b, c, d, e, f, g, h, i) = 'True
    IsMophableTuple (a, b, c, d, e, f, g, h, i, j) = 'True
    IsMophableTuple (a, b, c, d, e, f, g, h, i, j, k) = 'True
    IsMophableTuple (a, b, c, d, e, f, g, h, i, j, k, l) = 'True
    IsMophableTuple (a, b, c, d, e, f, g, h, i, j, k, l, m) = 'True
    IsMophableTuple (a, b, c, d, e, f, g, h, i, j, k, l, m, n) = 'True
    IsMophableTuple (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o) = 'True
    IsMophableTuple (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p) = 'True
    IsMophableTuple (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q) = 'True
    IsMophableTuple (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r) = 'True
    IsMophableTuple (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s) = 'True
    IsMophableTuple (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t) = 'True
    IsMophableTuple (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u) = 'True
    IsMophableTuple (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v) = 'True
    IsMophableTuple (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w) = 'True
    IsMophableTuple (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x) = 'True
    IsMophableTuple (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y) = 'True
    IsMophableTuple (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z) = 'True
    IsMophableTuple (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a1) = 'True
    IsMophableTuple (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a1, b1) = 'True
    IsMophableTuple (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a1, b1, c1) = 'True
    IsMophableTuple (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a1, b1, c1, d1) = 'True
    IsMophableTuple (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a1, b1, c1, d1, e1) = 'True
    IsMophableTuple (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a1, b1, c1, d1, e1, f1) = 'True
    IsMophableTuple (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a1, b1, c1, d1, e1, f1, g1) = 'True
    IsMophableTuple (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a1, b1, c1, d1, e1, f1, g1, h1) = 'True
    IsMophableTuple (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a1, b1, c1, d1, e1, f1, g1, h1, i1) = 'True
    IsMophableTuple (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a1, b1, c1, d1, e1, f1, g1, h1, i1, j1) = 'True
    IsMophableTuple (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a1, b1, c1, d1, e1, f1, g1, h1, i1, j1, k1) = 'True
    IsMophableTuple (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a1, b1, c1, d1, e1, f1, g1, h1, i1, j1, k1, l1) = 'True
    IsMophableTuple (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a1, b1, c1, d1, e1, f1, g1, h1, i1, j1, k1, l1, m1) = 'True
    IsMophableTuple (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a1, b1, c1, d1, e1, f1, g1, h1, i1, j1, k1, l1, m1, n1) = 'True
    IsMophableTuple (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a1, b1, c1, d1, e1, f1, g1, h1, i1, j1, k1, l1, m1, n1, o1) = 'True
    IsMophableTuple (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a1, b1, c1, d1, e1, f1, g1, h1, i1, j1, k1, l1, m1, n1, o1, p1) = 'True
    IsMophableTuple (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a1, b1, c1, d1, e1, f1, g1, h1, i1, j1, k1, l1, m1, n1, o1, p1, q1) = 'True
    IsMophableTuple (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a1, b1, c1, d1, e1, f1, g1, h1, i1, j1, k1, l1, m1, n1, o1, p1, q1, r1) = 'True
    IsMophableTuple (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a1, b1, c1, d1, e1, f1, g1, h1, i1, j1, k1, l1, m1, n1, o1, p1, q1, r1, s1) = 'True
    IsMophableTuple (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a1, b1, c1, d1, e1, f1, g1, h1, i1, j1, k1, l1, m1, n1, o1, p1, q1, r1, s1, t1) = 'True
    IsMophableTuple (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a1, b1, c1, d1, e1, f1, g1, h1, i1, j1, k1, l1, m1, n1, o1, p1, q1, r1, s1, t1, u1) = 'True
    IsMophableTuple (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a1, b1, c1, d1, e1, f1, g1, h1, i1, j1, k1, l1, m1, n1, o1, p1, q1, r1, s1, t1, u1, v1) = 'True
    IsMophableTuple (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a1, b1, c1, d1, e1, f1, g1, h1, i1, j1, k1, l1, m1, n1, o1, p1, q1, r1, s1, t1, u1, v1, w1) = 'True
    IsMophableTuple (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a1, b1, c1, d1, e1, f1, g1, h1, i1, j1, k1, l1, m1, n1, o1, p1, q1, r1, s1, t1, u1, v1, w1, x1) = 'True
    IsMophableTuple (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a1, b1, c1, d1, e1, f1, g1, h1, i1, j1, k1, l1, m1, n1, o1, p1, q1, r1, s1, t1, u1, v1, w1, x1, y1) = 'True
    IsMophableTuple (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a1, b1, c1, d1, e1, f1, g1, h1, i1, j1, k1, l1, m1, n1, o1, p1, q1, r1, s1, t1, u1, v1, w1, x1, y1, z1) = 'True
    IsMophableTuple (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a1, b1, c1, d1, e1, f1, g1, h1, i1, j1, k1, l1, m1, n1, o1, p1, q1, r1, s1, t1, u1, v1, w1, x1, y1, z1, a2) = 'True
    IsMophableTuple (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a1, b1, c1, d1, e1, f1, g1, h1, i1, j1, k1, l1, m1, n1, o1, p1, q1, r1, s1, t1, u1, v1, w1, x1, y1, z1, a2, b2) = 'True
    IsMophableTuple (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a1, b1, c1, d1, e1, f1, g1, h1, i1, j1, k1, l1, m1, n1, o1, p1, q1, r1, s1, t1, u1, v1, w1, x1, y1, z1, a2, b2, c2) = 'True
    IsMophableTuple (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a1, b1, c1, d1, e1, f1, g1, h1, i1, j1, k1, l1, m1, n1, o1, p1, q1, r1, s1, t1, u1, v1, w1, x1, y1, z1, a2, b2, c2, d2) = 'True
    IsMophableTuple (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a1, b1, c1, d1, e1, f1, g1, h1, i1, j1, k1, l1, m1, n1, o1, p1, q1, r1, s1, t1, u1, v1, w1, x1, y1, z1, a2, b2, c2, d2, e2) = 'True
    IsMophableTuple (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a1, b1, c1, d1, e1, f1, g1, h1, i1, j1, k1, l1, m1, n1, o1, p1, q1, r1, s1, t1, u1, v1, w1, x1, y1, z1, a2, b2, c2, d2, e2, f2) = 'True
    IsMophableTuple (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a1, b1, c1, d1, e1, f1, g1, h1, i1, j1, k1, l1, m1, n1, o1, p1, q1, r1, s1, t1, u1, v1, w1, x1, y1, z1, a2, b2, c2, d2, e2, f2, g2) = 'True
    IsMophableTuple (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a1, b1, c1, d1, e1, f1, g1, h1, i1, j1, k1, l1, m1, n1, o1, p1, q1, r1, s1, t1, u1, v1, w1, x1, y1, z1, a2, b2, c2, d2, e2, f2, g2, h2) = 'True
    IsMophableTuple (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a1, b1, c1, d1, e1, f1, g1, h1, i1, j1, k1, l1, m1, n1, o1, p1, q1, r1, s1, t1, u1, v1, w1, x1, y1, z1, a2, b2, c2, d2, e2, f2, g2, h2, i2) = 'True
    IsMophableTuple (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, a1, b1, c1, d1, e1, f1, g1, h1, i1, j1, k1, l1, m1, n1, o1, p1, q1, r1, s1, t1, u1, v1, w1, x1, y1, z1, a2, b2, c2, d2, e2, f2, g2, h2, i2, j2) = 'True
    IsMophableTuple c = 'False
