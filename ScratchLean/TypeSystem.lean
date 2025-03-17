import Lean

section vars

variable (a : Sort 0)
variable (b : Sort 1)
variable (c : Sort 2)

end vars

-- names of sorts
#check Sort 0 = Prop

#check Type 0 = Sort 1
#check Type = Sort 1

#check Type 1 = Sort 2

-- types of types
#check Prop
#check Type


-- instances of types (sorts)
#check True
#check Nat

-- instances of types (which are instances of sorts)
#check True.intro
#check 0

-- propositions have type prop
-- proofs have type proposition, and *proofs with same type are always equal*

-- functions
def id_nat₁ (x : Nat) : Nat := x
def id_nat₂ : Nat → Nat := fun (x: Nat) => x
def id_nat₃ : Nat → Nat := λ x ↦ x

#check id_nat₁
#check Nat → Nat

-- type of function types is max of type of all types inside OR prop if final type is a proposition
#check Nat → Nat
#check Nat → Type
#check Type → Nat
#check Prop → Nat
#check Nat → Prop

#check True → Nat
#check Nat → True

-- polymorphic type in function
section
universe u v
def f_type_u_v (a : Type u) (b : Type v) : Type u := a

#check f_type_u_v
#check f_type_u_v.{1, 2}
#check Type u → Type v → Type u

def f_sort_u_v : Sort u → Sort v → Sort u := fun a => fun b => a

#check f_sort_u_v
#check f_sort_u_v.{1, 2}
#check Sort u → Sort v → Sort u
end

-- generalizing a function via dependent types and universes
section
def id₁ (x : Nat) : Nat := x
#check id₁
#check Nat → Nat
#eval id₁ 5

def id₂ (α : Type) (x : α) : α := x

#check id₂
#check (α : Type) → α → α
#eval id₂ Bool true

universe u

def id₃ (α : Sort u) (x : α) : α := x
#check id₃
#check (α : Sort u) → α → α
#check id₃ True True.intro

end

-- more dependent type examples
section
def typeMapper (b: Bool) : Type :=
  match b with
  | true => Prop
  | false => Nat

def f (b : Bool) : typeMapper b :=
  match b with
  | true => True
  | false => (0 : Nat)

#check f
#check (b : Bool) → typeMapper b

end

-- implicit arguments for dependent types
section

def g {α β : Type} (f : α → β) (x : α) : β := f x
#check g
#check {α β : Type} → (α → β) → α → β

#check g id₁ 1
#check @g Nat Nat id₁ 1

end

section
-- inductive types with constant construtors
inductive Shape where
| circle : Shape
| triangle
| rectangle : Shape

#check Shape
#check Shape.circle

-- inductive type with construtors
inductive NBNP where
| none : NBNP
| nat : Nat → NBNP
| bool (x: Bool) : NBNP
| prop (x: Prop)

#check NBNP

#check NBNP.none

#check NBNP.nat
#check NBNP.nat 2

#check NBNP.bool
#check NBNP.bool true

#check NBNP.prop
#check NBNP.prop False

-- forcing inductive type to live as a Sort beside Type (= Sort 1)
inductive ShapeAsProp: Sort 0 where
| circle
| triangle
| rectangle

#check ShapeAsProp
#check ShapeAsProp.circle

-- structure is inductive type with only one constructor and accessor functions defined
structure Color where
  ctor ::
  red : Nat
  blue : Nat
  green : Nat

#check Color

#check Color.ctor
#check Color.ctor 1 2 3

#check Color.red
#eval Color.red (Color.ctor 1 2 3)
#check fun (c : Color) => c.red

end

section
-- inductive types can be "indexed", note the index is implicit
inductive FoundNumber (n : Nat) where
| unknown
| known (b : Bool)

#check FoundNumber
#check FoundNumber 5

#check FoundNumber.unknown
#check @FoundNumber.unknown 5

#check FoundNumber.known
#check FoundNumber.known true
#check @FoundNumber.known 5 true

-- equivalent defining inductive types
inductive FoundNumber' : Nat → Type where
| unknown : FoundNumber' n
| known (b : Bool) : FoundNumber' n

-- structure can also be indexed
structure Vector2D (α : Type) where
mk ::
(x : α)
(y : α)

#check Vector2D
#check Vector2D Nat

#check Vector2D.mk 2 3
#check @Vector2D.mk Nat 2 3

-- indexing vs constructor args, while all 3 "hold" two numbers, only first is a fixed type, while other two change types according to what they are holding
inductive PairNat₁ : Type where
| pair (a b : Nat)

inductive PairNat₂ (a : Nat) : Type where
| pair (b : Nat)

inductive PairNat₃ (a b : Nat) : Type where
| pair

-- dependent typing and implicitness in inductive types
inductive IsGood {α : Type} (x : α) where
| wrap

#check IsGood
#check @IsGood Nat
#check IsGood 3
#check @IsGood Nat 3

#check (IsGood.wrap : IsGood 3)
#check @IsGood.wrap Nat 3

-- complex dependent typing
inductive VectorND (α : Type) : Nat → Type
| nil  : VectorND α 0
| mk : α → VectorND α n → VectorND α (n+1)

#check VectorND
#check VectorND Nat
#check VectorND Nat 2

#check (VectorND.nil : VectorND Nat 0)
#check VectorND.mk 10 (VectorND.mk 20 VectorND.nil) -- (10, 20)

end


-- typeclass are really just types
-- they can be bunch of facts together (basically structure)
class TrueIsProvable where
  proofOfTrue : True

#check TrueIsProvable
#check TrueIsProvable.proofOfTrue
#check TrueIsProvable.mk

def funUsingTrueIsProvable [TrueIsProvable] : True := TrueIsProvable.proofOfTrue

-- can provide instances for type classes, which will be inferred
instance instTrueIsProvable: TrueIsProvable where
  proofOfTrue := True.intro

#check instTrueIsProvable
#check instTrueIsProvable.proofOfTrue

#synth TrueIsProvable
#check funUsingTrueIsProvable = True.intro


-- typeclass is useful when it holds elements of some type, then it becaomes a type (not a proposition)
class SomePropIsProvable where
  p : Prop
  hp : p

#check SomePropIsProvable
#check SomePropIsProvable.mk
#check SomePropIsProvable.p
#check SomePropIsProvable.hp


-- note that inferred instance's p and hp are being used
def funUsingPropIsProvable [SomePropIsProvable] (x : Nat) : ∃ (p : Prop), p :=
  Exists.intro SomePropIsProvable.p SomePropIsProvable.hp

instance : SomePropIsProvable where
  p := True
  hp := True.intro

-- auto named
#synth SomePropIsProvable

#check funUsingPropIsProvable 3
#check @funUsingPropIsProvable inferInstance 3
#check @funUsingPropIsProvable inferInstance 3

-- note can define many instances, last one becomes default
instance otherInstPropIsProvable: SomePropIsProvable where
  p := False → False
  hp := fun h => h

#synth SomePropIsProvable

-- classes should utlize indices to be really useful
class BetterSomePropIsProvable (p : Prop) where
  hp : p

instance : BetterSomePropIsProvable True where
  hp := True.intro

instance : BetterSomePropIsProvable (False → False) where
  hp := fun h => h

#check BetterSomePropIsProvable
#check BetterSomePropIsProvable.hp
