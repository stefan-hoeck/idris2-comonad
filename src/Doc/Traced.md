## The `Traced` Comonad

In this post I'll have a look at the `Traced` comonad and
its uses as a functional analogue to the builder pattern
from object oriented programming.

This is a literate Idris2 file, therefore:

```idris
module Doc.Traced

import Control.Comonad
import Control.Comonad.Traced
import Control.Monad.Identity
```

### The Builder Pattern

Assume we build a computer game with some monster-crushing
heroes saving the world from doom.

```idris
data Gender = Female | Male | NonBinary

data Race = Human | Elf | Dwarf | Hobbit | HalfOrc

data Class = Warrior | Wizard | Thief | Cleric

data Curse = MagicMissiles | Darkness | Fireball

data Cure = Heal | RemoveCurse | Resurrection

SpellPointsType : Class -> Type
SpellPointsType Wizard  = Nat
SpellPointsType Cleric  = Nat
SpellPointsType Warrior = ()
SpellPointsType Thief   = ()

SpellsType : Class -> Type
SpellsType Wizard  = List Curse
SpellsType Cleric  = List Cure
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
```

That's quite a large list of fields, and in reality, it could
be much larger. We'll need some utility functions to conveniently
create `Hero` values. In addition, although we encoded some
data invariants at the type level (warriors will never cast
spells), we probably still want to keep the constructor private,
since we'd like to uphold some additional invariants.
For instance, me might want
the list of spells to be sorted and contain no duplicates.
These kind of things could (and should!) be encoded at the
type level, but we'd still rather not burden users of our
library with such bookkeeping.

We therefore need a way to safely and conveniently
build `Hero` values. For this, we define a
`Field` data type we can use to adjust hero
fields.

```idris
namespace Field
  public export
  data Field : Class -> Type -> Type where
    Name         : Field c String
    Gender       : Field c Gender
    Race         : Field c Race
    Level        : Field c Nat
    Age          : Field c Nat
    Strength     : Field c Nat
    Intelligence : Field c Nat
    HitPoint     : Field c Nat
    SpellPoints  : Field c (SpellPointsType c)
    Spells       : Field c (SpellsType c)
    Equipment    : Field c (List String)
  
record Setting (c : Class) where
  constructor Set
  fld : Field c t
  fun : t -> t

infixr 4 $>, :>

($>) : Field c t -> (t -> t) -> Setting c
($>) = Set

(:>) : Field c t -> t -> Setting c
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
dummy c =
  let (sp,sps) = vals
   in setAll (MkHeroC "name" Female Human 0 18 10 10 10 sp sps Nil)

  where vals : (SpellPointsType c, SpellsType c)
        vals = case c of
                    Wizard   => (0, [])
                    Cleric   => (0, [])
                    Thief    => ((),())
                    Warrior  => ((),())

warrior1 : HeroBuilder Warrior
warrior1 ss = dummy Warrior (ss <+> [ HitPoint $> (+10)
                                    , Equipment $> ("Sword" ::)])

halfOrcWarrior1 : HeroBuilder Warrior
halfOrcWarrior1 ss = warrior1 (ss <+>
  [Strength $> (+5), Intelligence $> (`minus` 5), Race :> HalfOrc])
```

That's quite ugly. Half-orcs are not always warriors. So we'll also
need `halfOrcWizard` eventually. This does not compose at all
and leads to an explosion of combinations. Perhaps we need
a way to apply additional settings to an existing builder:

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
extendBuilder : (HeroBuilder c -> HeroC c) -> HeroBuilder c -> HeroBuilder c
extendBuilder makeHero builder settings =
  makeHero (\ss => builder (ss <+> settings))

runBuilder : HeroBuilder c -> HeroC c
runBuilder f = f []

orshosh1 : HeroC Warrior
orshosh1 = runBuilder ( extendBuilder warrior2 
                      . extendBuilder halfOrc2 
                      . extendBuilder male2 $ dummy Warrior
                      )
```

That's slightly better. But there seems to be a pattern hidden
here. And we need better syntax. Sounds like an interface we
are looking for. The pattern is the following:

```idris
run : Monoid m => (m -> a) -> a
run f = f neutral

doExtend : Semigroup m => ((m -> a) -> b) -> (m -> a) -> (m -> b)
doExtend mab ma = \m => mab (\m1 => ma (m <+> m1))
```

### Enter `Traced`

Functions `run` and `doExtend` are part of an interface called
`Comonad`, the categorical dual to `Monad`. The comonad representing
our builder example is the `Traced` comonad. (Actually, `TracedT`
is a comonad transformer. We could also use `Morphism`
from `Data.Morphism`, which behaves like `TracedT` over
`Identity`.) Let's give it a try:

```idris
Builder : Class -> Type -> Type
Builder c = Traced (List $ Setting c)

runWith : m -> Traced m a -> a
runWith = flip runTraced

blank : {c : Class} -> Builder c (HeroC c)
blank {c} = traced (dummy c)

warrior : Builder Warrior a -> a
warrior = runWith [ HitPoint     $> (+10)
                  , Strength     $> (+3)
                  , Intelligence $> (`minus` 3)
                  , Equipment    $> ("Sword" ::)
                  ]

wizard : Builder Wizard a -> a
wizard = runWith [ HitPoint     $> (`minus` 5)
                 , Strength     $> (`minus` 3)
                 , Intelligence $> (+3)
                 , SpellPoints  $> (+ 10)
                 , Spells       $> (MagicMissiles ::)
                 ]

halfOrc : Builder c a -> a
halfOrc = runWith [ Strength     $> (+5)
                  , Intelligence $> (`minus` 5)
                  , Race         :> HalfOrc
                  ]

elf : Builder c a -> a
elf = runWith [ Strength     $> (`minus` 2)
              , Intelligence $> (+3)
              , Race         :> Elf
              ]

gender : Gender -> Builder c a -> a
gender g = runWith [Gender :> g]

name : String -> Builder c a -> a
name g = runWith [Name :> g]

orshosh : HeroC Warrior
orshosh = extract $   blank
                  =>> warrior
                  =>> halfOrc
                  =>> gender Male
                  =>> name "Orshosh"

lucie : HeroC Wizard
lucie = extract $   blank
                =>> wizard
                =>> elf
                =>> gender Female
                =>> name "Lucie"
```

This, of course, resembles the [Builder Pattern](https://en.wikipedia.org/wiki/Builder_pattern)
from object oriented programming, and indeed, there seems to be
an interesting connection between object oriented encapsulation
and comonads. This is also being elaborated on
in [a blog post by Gabriel Gonzales](https://www.haskellforall.com/2013/02/you-could-have-invented-comonads.html).

While monads allow us to put data in a context, comonads
allow us to take data out of its context. With just the `Monad`
interface, it is impossible to get data out of its context,
while with only the `Comonad` interface it is impossible
to get data into a context. From this point of view, `Monad`s
consume data while `Comonad`s produce data. Therefore, we
probably should have a look at the link between `Comonads`
and codata.
