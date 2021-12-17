module Control.Comonad.Traced.Traced

import Control.Comonad
import Control.Comonad.Trans
import Control.Monad.Identity

%default total

public export
record TracedT (m : Type) (w : Type -> Type) (a : Type) where
  constructor MkTracedT
  runTracedT : w (m -> a)

public export
Traced : (m : Type) -> (a : Type) -> Type
Traced m = TracedT m Identity

public export %inline
traced : (m -> a) -> Traced m a
traced f = MkTracedT (Id f)

public export %inline
runTraced : Traced m a -> m -> a
runTraced (MkTracedT (Id f)) = f

--------------------------------------------------------------------------------
--          Utilities
--------------------------------------------------------------------------------

public export %inline
listen : Functor w => TracedT m w a -> TracedT m w (a, m)
listen = { runTracedT $= map (\f,m => (f m, m)) }

public export %inline
listens : Functor w => (m -> b) -> TracedT m w a -> TracedT m w (a, b)
listens g = { runTracedT $= map (\f,m => (f m, g m)) }

public export %inline
censor : Functor w => (m -> m) -> TracedT m w a -> TracedT m w a
censor g = { runTracedT $= map (. g) }

--------------------------------------------------------------------------------
--          Interface Implementations
--------------------------------------------------------------------------------

appEnv : (s -> a -> b) -> (s -> a) -> s -> b
appEnv ff fa s = ff s (fa s)

public export %inline
Functor w => Functor (TracedT m w) where
  map f = { runTracedT $= map (f .) }

public export %inline
Applicative w => Applicative (TracedT m w) where
  pure = MkTracedT . pure . const
  MkTracedT wf <*> MkTracedT wa = MkTracedT (map appEnv wf <*> wa)

public export %inline
(Comonad w, Monoid m) => Comonad (TracedT m w) where
  extract (MkTracedT wf) = extract wf neutral
  extend f =
    { runTracedT $= extend (\w,m => f (MkTracedT $ map (. (<+> m)) w)) }

public export %inline
(ComonadApply w, Monoid m) => ComonadApply (TracedT m w) where
  MkTracedT wf <@> MkTracedT wa = MkTracedT (map appEnv wf <@> wa)

public export %inline
Monoid m => ComonadTrans (TracedT m) where
  lower = map ($ neutral) . runTracedT
