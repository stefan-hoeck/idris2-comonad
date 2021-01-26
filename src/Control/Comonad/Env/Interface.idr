module Control.Comonad.Env.Interface

import Control.Comonad
import Control.Comonad.Env.Env

%default total

public export
interface Comonad w => ComonadEnv e w | w where
  ask : w a -> e

public export
asks : ComonadEnv e w => (e -> e') -> w a -> e'
asks = (. ask)

--------------------------------------------------------------------------------
--          Implementations
--------------------------------------------------------------------------------

public export
Comonad w => ComonadEnv e (EnvT e w) where
  ask = env
