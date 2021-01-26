module Control.Comonad.Env.Env

import Control.Comonad
import Control.Comonad.Trans
import Control.Monad.Identity

%default total

public export
record EnvT (e : Type) (w : Type -> Type) (a : Type)  where
  constructor MkEnvT
  env : e
  val : w a

public export
Env : (e : Type) -> (a : Type) -> Type
Env e = EnvT e Identity

||| Create an Env using an environment and a value
public export
mkEnv : e -> a -> Env e a
mkEnv e a = MkEnvT e (Id a)

public export
runEnv : Env e a -> (e, a)
runEnv (MkEnvT e (Id a)) = (e, a)

public export
runEnvT : EnvT e w a -> (e, w a)
runEnvT (MkEnvT e wa) = (e, wa)

||| Modifies the environment using the specified function.
public export
local : (e -> e') -> EnvT e w a -> EnvT e' w a
local f = record { env $= f}

--------------------------------------------------------------------------------
--          Interface Implementations
--------------------------------------------------------------------------------

public export
Functor w => Functor (EnvT e w) where
  map g (MkEnvT e wa) = MkEnvT e (map g wa)

public export
(Monoid e, Applicative m) => Applicative (EnvT e m) where
  pure = MkEnvT neutral . pure
  MkEnvT ef wf <*> MkEnvT ea wa = MkEnvT (ef <+> ea) (wf <*> wa)

public export
Foldable w => Foldable (EnvT e w) where
  foldl f acc = foldl f acc . val
  foldr f acc = foldr f acc . val
  null        = null . val

public export
Traversable w => Traversable (EnvT e w) where
  traverse f (MkEnvT e w) = MkEnvT e <$> traverse f w

public export
Comonad w => Comonad (EnvT e w) where
  duplicate (MkEnvT e wa) = MkEnvT e (extend (MkEnvT e) wa)
  extract = extract . val

public export
ComonadTrans (EnvT e) where
  lower (MkEnvT _ wa) = wa

public export
(Semigroup e, ComonadApply w) => ComonadApply (EnvT e w) where
  MkEnvT ef wf <@> MkEnvT ea wa = MkEnvT (ef <+> ea) (wf <@> wa)
