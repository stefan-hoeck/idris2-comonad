module Control.Comonad.Store.Store

import Control.Comonad
import Control.Comonad.Trans
import Control.Monad.Identity

%default total

public export
record StoreT (s : Type) (w : Type -> Type) (a : Type) where
  constructor MkStoreT
  run : w (s -> a)
  val : s

public export
Store : (s : Type) -> (a : Type) -> Type
Store s = StoreT s Identity

||| Create a Store using an accessor function and a stored value
public export
store : (s -> a) -> s -> Store s a
store f s = MkStoreT (Id f) s

public export
runStore : Store s a -> (s -> a, s)
runStore (MkStoreT (Id f) s) = (f, s)

public export
runStoreT : StoreT s w a -> (w (s -> a), s)
runStoreT (MkStoreT wf s) = (wf, s)

--------------------------------------------------------------------------------
--          Interface Implementations
--------------------------------------------------------------------------------

public export
Functor w => Functor (StoreT s w) where
  map f = { run $= map (f .) }

appEnv : (s -> a -> b) -> (s -> a) -> s -> b
appEnv ff fa s = ff s (fa s)

public export
(Monoid s, Applicative w) => Applicative (StoreT s w) where
  pure a = MkStoreT (pure $ const a) neutral
  MkStoreT f m <*> MkStoreT a n = MkStoreT [| appEnv f a |]  (m <+> n)

public export
Comonad w => Comonad (StoreT s w) where
  extract (MkStoreT wf s)   = extract wf s
  duplicate (MkStoreT wf s) = MkStoreT (extend MkStoreT wf) s
  extend f (MkStoreT wf s)  =
    MkStoreT (extend (\wf',s' => f (MkStoreT wf' s')) wf) s

public export
ComonadTrans (StoreT s) where
  lower (MkStoreT f s) = map ($ s) f

public export
(ComonadApply w, Semigroup s) => ComonadApply (StoreT s w) where
  MkStoreT f m <@> MkStoreT a n = MkStoreT (map appEnv f <@> a) (m <+> n)
