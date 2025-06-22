namespace Note

structure MythicalCreature : Type where
  large : Bool
deriving Repr

structure Monster extends MythicalCreature where
  vulnerability : String
deriving Repr
#check Monster.mk

def troll : Monster where
  large := Bool.true
  vulnerability := "sunlight"

#eval troll.large
-- #eval Monster.larget troll
-- #eval MythicalCreature.large troll

def MythicalCreature.small (mc : MythicalCreature) : Bool := !mc.large

-- #eval troll.small
-- #eval Monster.small troll
-- #eval MythicalCreature.small troll

structure Helper extends MythicalCreature where
  assistance : String
  payment : String
deriving Repr

def nisse : Helper where
  large := Bool.false
  assistance := "household tasks"
  payment := "porridge"

structure MonstrousAssistant extends Monster, Helper where
deriving Repr

def domesticatedTroll : MonstrousAssistant where
  large := Bool.false
  assistance := "heavy labor"
  payment := "toy goats"
  vulnerability := "sunlight"

#print MonstrousAssistant.toMonster
#print MonstrousAssistant.toHelper

inductive Size : Type where
| small : Size
| medium : Size
| large : Size
deriving BEq

structure SizedCreature extends MythicalCreature where
  size : Size
  large := size == Size.large

abbrev SizesMatch (sc : SizedCreature) : Prop :=
  sc.large = (sc.size == Size.large)

def nonsenseCreature : SizedCreature where
  large := Bool.false
  size := Size.large

def huldre : SizedCreature where
  size := Size.medium

example : SizesMatch huldre := by
  sorry

end Note
