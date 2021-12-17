module Control.Comonad.Store.Interface

import Control.Comonad
import Control.Comonad.Env.Env
import Control.Comonad.Store.Store
import Control.Comonad.Traced.Traced
import Control.Comonad.Trans

%default total

public export
interface Comonad w => ComonadStore s w | w where
  pos : w a -> s

  peek : s -> w a -> a

  peeks : (s -> s) -> w a -> a
  peeks f w = peek (f (pos w)) w

  seek : s -> w a -> w a
  seek s = peek s . duplicate

  seeks : (s -> s) -> w a -> w a
  seeks f = peeks f . duplicate

  experiment : Functor f => (s -> f s) -> w a -> f a
  experiment f w = map (`peek` w) (f (pos w))

--------------------------------------------------------------------------------
--          Utilities
--------------------------------------------------------------------------------

public export %inline
lowerPos : (ComonadTrans t, ComonadStore s w) => t w a -> s
lowerPos = pos . lower

public export %inline
lowerPeek : (ComonadTrans t, ComonadStore s w) => s -> t w a -> a
lowerPeek s = peek s . lower

public export %inline
lowerExperiment :  (ComonadTrans t, ComonadStore s w, Functor f)
                => (s -> f s) -> t w a -> f a
lowerExperiment f = experiment f . lower

--------------------------------------------------------------------------------
--          Implementations
--------------------------------------------------------------------------------

public export %inline
ComonadStore s w => ComonadStore s (EnvT e w) where
  pos        = lowerPos
  peek       = lowerPeek
  experiment = lowerExperiment

public export %inline
Comonad w => ComonadStore s (StoreT s w) where
  pos                          = val
  peek s (MkStoreT run _)      = extract run s
  seek s                       = { val := s }
  seeks f                      = { val $= f }
  experiment f (MkStoreT wf s) = extract wf <$> f s

public export %inline
(ComonadStore s w, Monoid m) => ComonadStore s (TracedT m w) where
  pos        = lowerPos
  peek       = lowerPeek
  experiment = lowerExperiment
