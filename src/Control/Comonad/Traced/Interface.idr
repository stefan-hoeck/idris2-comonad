module Control.Comonad.Traced.Interface

import Data.Morphisms

import Control.Comonad
import Control.Comonad.Env.Env
import Control.Comonad.Store.Store
import Control.Comonad.Traced.Traced
import Control.Comonad.Trans

%default total

interface Comonad w => ComonadTraced m w | w where
  trace : m -> w a -> a

--------------------------------------------------------------------------------
--          Utilities
--------------------------------------------------------------------------------

public export %inline
traces : ComonadTraced m w => (a -> m) -> w a -> a
traces f wa = trace (f $ extract wa) wa

public export %inline
lowerTrace : (ComonadTrans t, ComonadTraced m w) => m -> t w a -> a
lowerTrace m = trace m . lower

--------------------------------------------------------------------------------
--          Implementations
--------------------------------------------------------------------------------

public export %inline
Monoid m => ComonadTraced m (Morphism m) where
  trace m (Mor f) = f m

public export %inline
ComonadTraced m w => ComonadTraced m (EnvT e w) where
  trace = lowerTrace

public export %inline
ComonadTraced m w => ComonadTraced m (StoreT s w) where
  trace = lowerTrace

public export %inline
(Comonad w, Monoid m) => ComonadTraced m (TracedT m w) where
  trace m (MkTracedT wf) = extract wf m
