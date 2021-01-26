module Control.Comonad.Trans

import Control.Comonad

%default total

public export
interface ComonadTrans (0 t : (Type -> Type) -> Type -> Type) where
  lower : Comonad w => t w a -> w a
