module Control.Comonad.Env.Interface

import Control.Comonad
import Control.Comonad.Env.Env
import Control.Comonad.Store.Store
import Control.Comonad.Traced.Traced
import Control.Comonad.Trans

%default total

public export
interface Comonad w => ComonadEnv e w | w where
  ask : w a -> e

public export %inline
asks : ComonadEnv e w => (e -> e') -> w a -> e'
asks = (. ask)

public export %inline
lowerAsk : (ComonadEnv e w, ComonadTrans t) => t w a -> e
lowerAsk = ask . lower

--------------------------------------------------------------------------------
--          Implementations
--------------------------------------------------------------------------------

public export %inline
Comonad w => ComonadEnv e (EnvT e w) where
  ask = env

public export %inline
ComonadEnv e w => ComonadEnv e (StoreT t w) where
  ask = lowerAsk {t = StoreT t}

public export %inline
(ComonadEnv e w, Monoid m) => ComonadEnv e (TracedT m w) where
  ask = lowerAsk {t = TracedT m}
