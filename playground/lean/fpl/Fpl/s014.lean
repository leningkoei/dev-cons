/-
Define a structure named `RectangularPrism` that contains the height, width, and
depth of a rectangular prism, each as a `Float`.
-/

structure RectangularPrism where
  height : Float
  width : Float
  depth : Float

def rectangularPrism := RectangularPrism.mk 1 2 3

#eval rectangularPrism

/-
Define a function named `volume : RectangularPrism → Float` that computers the
volume of a rectangular prism.
-/

def volume (rectangularPrism : RectangularPrism) : Float :=
  rectangularPrism.height * rectangularPrism.width * rectangularPrism.depth

#eval volume rectangularPrism

/-
Define a structure named `Segment` that represents a line segment by its
endpoints, and define a function `length : Segment → Float` that computes the
length of a line segment. `Segment` should have at most two fields.
-/

structure Point where
  x : Float
  y : Float

structure Segment where
  endpoint1 : Point
  endpoint2 : Point

def segment := Segment.mk (Point.mk 0 0) (Point.mk 1 1)

def Segment.length (segment : Segment) : Float :=
  let (x1, y1) := (segment.endpoint1.x, segment.endpoint1.y)
  let (x2, y2) := (segment.endpoint2.x, segment.endpoint2.y)
  ((x2 - x1) ^ 2 + (y2 - y1) ^ 2) ^ (1/2)

#eval segment.length

/-
Which names are introuduced by the declaration of `RectangularPrism`?
-/

#check RectangularPrism.mk
#check RectangularPrism.height
#check RectangularPrism.width
#check RectangularPrism.depth

/-
Which names are introuduced by the following delarations of `Hamster` and
`Book`? What are their types?
-/

structure Hamster where
  name : String
  fluffy : Bool

#check Hamster.mk
#check Hamster.name
#check Hamster.fluffy

structure Book where
  makeBook ::
  title : String
  author : String
  price : Float

#check Book.makeBook
#check Book.title
#check Book.author
#check Book.price
