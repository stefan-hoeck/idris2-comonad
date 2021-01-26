## The `Traced` Comonad

```idris
module Doc.Traced

import Control.Comonad
import Control.Comonad.Traced

import Data.DPair
```

### The Builder Pattern

Assume we build a computer game with some monster-crushing
heroes saving the world from doom.

```idris
data Gender = Female | Male | NonBinary

data Class = Warrior | Wizard | Thief | Cleric

SpellPointsType : Class -> Type
SpellPointsType Wizard  = Nat
SpellPointsType Cleric  = Nat
SpellPointsType Warrior = ()
SpellPointsType Thief   = ()

SpellsType : Class -> Type
SpellsType Wizard  = List String
SpellsType Cleric  = List String
SpellsType Warrior = ()
SpellsType Thief   = ()

record Hero where
  constructor MkHero
  name        : String
  class       : Class
  gender      : Gender
  level       : Nat
  age         : Nat
  hitPoints   : Nat
  spellPoints : SpellPointsType class
  spells      : SpellsType class
  equipment   : List String

HeroC : Class -> Type
HeroC c = Subset Hero (\h => h.class = c)
```

That's quite a large list of fields, and in reality, it could
be much larger. We'll need some utility functions to conveniently
create `Hero` values. In additiona, although we encoded some
data invariants at the type level (warriors will never cast
spells), we probably want to keep the constructor private,
since we do not want client code to arbitrarily change
the `class` field of `Hero` values. In addition, we'd like to
uphole some additional invariants. For instance, me might want
the list of spells to be sorted and contain no duplicates.
These kind of things could (and should!) be encoded at the
type level, but we'd still rather not burden ourselves with
such bookkeeping at other places in the code.

We therefore need a way to safely and conveniently
build `Hero` values. For this, we define an
`Option` data type we can use to adjust hero
fields. The code in the next block was a lovely
exercise in dependently typed programming.

```idris
namespace Option
  data Option : Class -> Type -> Type where
    Name        : Option c String
    Gender      : Option c Traced.Gender
    Level       : Option c Nat
    Age         : Option c Nat
    HitPoint    : Option c Nat
    SpellPoints : Option c (SpellPointsType c)
    Spells      : Option c (SpellsType c)
    Equipment   : Option c (List String)
  
  record Setting (c : Class) where
    constructor Set
    opt : Option c t
    fun : t -> t

  ($>) : Option c t -> (t -> t) -> Setting c
  ($>) = Set

  (:>) : Option c t -> t -> Setting c
  (:>) o v = Set o (const v)

  public export
  set : (h : Hero) -> Setting (h.class) -> Hero
  set h (Set Name f)        = record { name $= f } h
  set h (Set Gender f)      = record { gender $= f } h
  set h (Set Level f)       = record { level $= f } h
  set h (Set Age f)         = record { age $= f } h
  set h (Set HitPoint f)    = record { hitPoints $= f } h
  set h (Set SpellPoints f) = record { spellPoints $= f } h
  set h (Set Spells f)      = record { spells $= f } h
  set h (Set Equipment f)   = record { equipment $= f } h

  -- proof that settings never affect a hero's class
  -- we'll need this when we apply lists of settings
  classUnchanged :  (h : Hero) -> (s : Setting (h.class))
                 -> (set h s).class = h.class
  classUnchanged (MkHero a b c d e x g h i) (Set Name f)        = Refl
  classUnchanged (MkHero a b c d e x g h i) (Set Gender f)      = Refl
  classUnchanged (MkHero a b c d e x g h i) (Set Level f)       = Refl
  classUnchanged (MkHero a b c d e x g h i) (Set Age f)         = Refl
  classUnchanged (MkHero a b c d e x g h i) (Set HitPoint f)    = Refl
  classUnchanged (MkHero a b c d e x g h i) (Set SpellPoints f) = Refl
  classUnchanged (MkHero a b c d e x g h i) (Set Spells f)      = Refl
  classUnchanged (MkHero a b c d e x g h i) (Set Equipment f)   = Refl

  sets : (h : Hero) -> List (Setting h.class) -> Hero
  sets h = fst . foldl accum (Element h Refl)
    where H : Type
          H = Subset Hero (\g => g.class = h.class)

          accum : H -> Setting h.class -> H
          accum (Element x refl) s =
            let s' = rewrite refl in s
             in Element (set x s') (rewrite sym refl in classUnchanged x s')
```

Ok, lets build some heroes.

```idris
-- dummy : (c : Class) -> List (Setting c) -> Hero
-- dummy c ss = let (sp,sps) = vals
--                  ini = MkHero "name" c Female 0 18 10 sp sps Nil
--               in sets ini ss
-- 
--   where vals : (SpellPointsType c, SpellsType c)
--         vals = case c of
--                     Wizard   => (20, ["Fireball"])
--                     Cleric   => (10, ["Cure"])
--                     Thief    => ((),())
--                     Warrior  => ((),())
```
