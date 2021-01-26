module Control.Comonad

import Control.Monad.Identity

import Data.List1
import Data.Morphisms
import Data.Stream

%default total

--------------------------------------------------------------------------------
--          Comonad
--------------------------------------------------------------------------------

public export
interface Functor w => Comonad w where
  extract   : w a -> a

  duplicate : w a -> w (w a)
  duplicate = extend id

  extend    : (w a -> b) -> w a -> w b
  extend f = map f . duplicate

--------------------------------------------------------------------------------
--          Comonad Implementations
--------------------------------------------------------------------------------

public export
Comonad (Pair e) where
  extract         = snd
  duplicate (e,a) = (e, (e, a))

public export
Comonad Identity where
  extract   = runIdentity
  duplicate = Id

public export
Comonad Stream where
  extract               = head
  duplicate xs@(_ :: t) = xs :: duplicate t

public export
Comonad List1 where
  extract = head
  duplicate (x ::: xs) = (x ::: xs) ::: tails xs
    where tails : List a -> List (List1 a)
          tails []        = []
          tails (x :: xs) = (x ::: xs) :: tails xs

public export
Monoid e => Comonad (Morphism e) where
  extract   (Mor f) = f neutral
  duplicate (Mor f) = Mor \e => Mor \e' => f (e <+> e')

--------------------------------------------------------------------------------
--          ComonadApply
--------------------------------------------------------------------------------

infixl 4 <@, @>, <@@>, <@>

public export
interface Comonad w => ComonadApply w where
  (<@>) : w (a -> b) -> w a -> w b

  (@>)  : w a -> w b -> w b
  (@>) = flip (<@)

  (<@) : w a -> w b -> w a
  a <@ b = map const a <@> b

--------------------------------------------------------------------------------
--          ComonadApply Implementations
--------------------------------------------------------------------------------

public export
Semigroup m => ComonadApply (Pair m) where
  (m, f) <@> (n, a) = (m <+> n, f a)
  (m, a) <@  (n, _) = (m <+> n, a)
  (m, _)  @> (n, b) = (m <+> n, b)

public export
ComonadApply List1 where
  (<@>) = (<*>)

public export
ComonadApply Stream where
  (<@>) = (<*>)

public export
Monoid m => ComonadApply (Morphism m) where
  (<@>) = (<*>)

public export
ComonadApply Identity where
  (<@>) = (<*>)
  _ @> b = b
  b <@ _ = b

--------------------------------------------------------------------------------
--          Utilities
--------------------------------------------------------------------------------

infixl 1 =>>
infixr 1 <<=, =<=, =>=

||| `extend` with the arguments swapped. Dual to `>>=` for a `Monad`.
public export %inline
(=>>) : Comonad w => w a -> (w a -> b) -> w b
(=>>) = flip extend

||| `extend` in operator form
public export %inline
(<<=) : Comonad w => (w a -> b) -> w a -> w b
(<<=) = extend

||| Right-to-left `Cokleisli` composition
public export %inline
(=<=) : Comonad w => (w b -> c) -> (w a -> b) -> w a -> c
f =<= g = f . extend g

||| Left-to-right `Cokleisli` composition
public export %inline
(=>=) : Comonad w => (w a -> b) -> (w b -> c) -> w a -> c
f =>= g = g . extend f

||| Flipped version of `<@>`.
public export %inline
(<@@>) : ComonadApply w => w a -> w (a -> b) -> w b
(<@@>) = flip (<@>)
