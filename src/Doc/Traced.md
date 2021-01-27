## The `Traced` Comonad

```idris
module Doc.Traced

import Control.Comonad
import Control.Comonad.Traced
import Control.Monad.Identity

import Data.DPair
```

### The Builder Pattern

Assume we build a computer game with some monster-crushing
heroes saving the world from doom.

```idris
data Gender = Female | Male | NonBinary

data Race = Human | Elf | Dwarf | Hobbit | HalfOrc

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

record HeroC (c : Class) where
  constructor MkHeroC
  name         : String
  gender       : Gender
  race         : Race
  level        : Nat
  age          : Nat
  hitPoints    : Nat
  strength     : Nat
  intelligence : Nat
  spellPoints  : SpellPointsType c
  spells       : SpellsType c
  equipment    : List String

record Hero where
  constructor MkHero
  class  : Class
  fields : HeroC class
```

That's quite a large list of fields, and in reality, it could
be much larger. We'll need some utility functions to conveniently
create `Hero` values. In additiona, although we encoded some
data invariants at the type level (warriors will never cast
spells), we probably want to keep the constructor private,
since we'd like to uphole some additional invariants.
For instance, me might want
the list of spells to be sorted and contain no duplicates.
These kind of things could (and should!) be encoded at the
type level, but we'd still rather not burden users of our
library with such bookkeeping.

We therefore need a way to safely and conveniently
build `Hero` values. For this, we define an
`Option` data type we can use to adjust hero
fields. The code in the next block was a lovely
exercise in dependently typed programming.

```idris
namespace Option
  public export
  data Option : Class -> Type -> Type where
    Name         : Option c String
    Gender       : Option c Gender
    Race         : Option c Race
    Level        : Option c Nat
    Age          : Option c Nat
    Strength     : Option c Nat
    Intelligence : Option c Nat
    HitPoint     : Option c Nat
    SpellPoints  : Option c (SpellPointsType c)
    Spells       : Option c (SpellsType c)
    Equipment    : Option c (List String)
  
record Setting (c : Class) where
  constructor Set
  opt : Option c t
  fun : t -> t

infixr 4 $>, :>

($>) : Option c t -> (t -> t) -> Setting c
($>) = Set

(:>) : Option c t -> t -> Setting c
(:>) o v = Set o (const v)

set : Setting c -> HeroC c -> HeroC c
set (Set Name f)         = record { name $= f }
set (Set Gender f)       = record { gender $= f }
set (Set Race f)         = record { race $= f }
set (Set Level f)        = record { level $= f }
set (Set Age f)          = record { age $= f }
set (Set Strength f)     = record { strength $= f }
set (Set Intelligence f) = record { intelligence $= f }
set (Set HitPoint f)     = record { hitPoints $= f }
set (Set SpellPoints f)  = record { spellPoints $= f }
set (Set Spells f)       = record { spells $= f }
set (Set Equipment f)    = record { equipment $= f }

HeroBuilder : Class -> Type
HeroBuilder c = List (Setting c) -> HeroC c

setAll : HeroC c -> HeroBuilder c
setAll = foldl (flip set)
```

Ok, lets build some heroes.

```idris
dummy : (c : Class) -> HeroBuilder c
dummy c = let (sp,sps) = vals
           in setAll (MkHeroC "name" Female Human 0 18 10 10 10 sp sps Nil)

  where vals : (SpellPointsType c, SpellsType c)
        vals = case c of
                    Wizard   => (0, [])
                    Cleric   => (0, [])
                    Thief    => ((),())
                    Warrior  => ((),())

warrior1 : HeroBuilder Warrior
warrior1 ss = dummy Warrior (ss <+> [HitPoint $> (+10), Equipment $> ("Sword" ::)])

halfOrcWarrior1 : HeroBuilder Warrior
halfOrcWarrior1 ss = warrior1 (ss <+>
  [Strength $> (+5), Intelligence $> (`minus` 5), Race :> HalfOrc])
```

That's quite ugly. Half-orcs are not always warriors. So we'll also
need `halfOrcWizard` eventually. This does not compose well
and leads to an explosion of combinations. What we'd actually like,
is some way to apply additional settings to an existing builder:

```idris
warrior2 : HeroBuilder Warrior -> HeroC Warrior
warrior2 b = b [HitPoint $> (+10), Equipment $> ("Sword" ::)]

halfOrc2 : HeroBuilder c -> HeroC c
halfOrc2 b = b [Strength $> (+5), Intelligence $> (`minus` 5), Race :> HalfOrc]

male2 : HeroBuilder c -> HeroC c
male2 b = b [Gender :> Male]
```

Ok, that's better, but it still does not compose. What we actually
need, are functions from builder to builder, which we can
then concatenate using function composition. Can we use our
already defined functions in such a new way?

```idris
extended : (HeroBuilder c -> HeroC c) -> HeroBuilder c -> HeroBuilder c
extended makeHero builder settings =
  makeHero (\ss => builder (ss <+> settings))

runBuilder : HeroBuilder c -> HeroC c
runBuilder f = f []

orshosh1 : HeroC Warrior
orshosh1 = runBuilder ( extended warrior2 
                      . extended halfOrc2 
                      . extended male2 $ dummy Warrior
                      )
```

That's slightly better. But there seems to be a pattern hidden
here. And we need better syntax. The pattern is the following:

```idris
run : Monoid m => (m -> a) -> a
run f = f neutral

doExtend : Semigroup m => ((m -> a) -> b) -> (m -> a) -> (m -> b)
doExtend f g h = f (\m => g (m <+> h))
```

### Enter `Traced`

Functions `run` and `doExtend` are part of an interface called
`Comonad`, the categorical dual to `Monad`. The comonad representing
this builder example is the `Traced` comonad. Let's give it
a try:

```idris
Builder : Class -> Type -> Type
Builder c = Traced (List $ Setting c)

runWith : m -> Traced m a -> a
runWith = flip runTraced

blank : (c : Class) -> Builder c (HeroC c)
blank c = traced (dummy c)

warrior : Builder Warrior a -> a
warrior = runWith [HitPoint $> (+10), Equipment $> ("Sword" ::)]

halfOrc : Builder c a -> a
halfOrc = runWith [ Strength $> (+5)
                  , Intelligence $> (`minus` 5)
                  , Race :> HalfOrc
                  ]

gender : Gender -> Builder c a -> a
gender g = runWith [Gender :> g]

name : String -> Builder c a -> a
name g = runWith [Name :> g]

orshosh : HeroC Warrior
orshosh = extract $   blank Warrior
                  =>> warrior
                  =>> halfOrc
                  =>> gender Male
                  =>> name "Orshosh"
```
