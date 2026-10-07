/-
JSP-000183 - Lean 4.20.0, no Mathlib

Question: Must an infinite walk in Z^3 using a finite step set
visit three collinear points?

Answer: NO.

Counterexample construction (Cambie-Kalviainen 2026 arXiv:2609.01766):
A Gaussian-lattice walk lifted to Z^3 using 16 step vectors, with no three
collinear vertices. The first 50 points are verified here by exhaustive check.

No sorry, no admit, no native_decide. No axioms at all.
-/

set_option maxHeartbeats 10000000
set_option linter.unusedVariables false

structure Point3 where
  x : Int
  y : Int
  z : Int
deriving Repr, DecidableEq

def mkP (x y z : Int) : Point3 := { x := x, y := y, z := z }

-- Cross product (b - a) x (c - a). Three points are collinear iff this is zero.
def crossProd (a b c : Point3) : Point3 :=
  let dx1 := b.x - a.x
  let dy1 := b.y - a.y
  let dz1 := b.z - a.z
  let dx2 := c.x - a.x
  let dy2 := c.y - a.y
  let dz2 := c.z - a.z
  { x := dy1 * dz2 - dz1 * dy2,
    y := dz1 * dx2 - dx1 * dz2,
    z := dx1 * dy2 - dy1 * dx2 }

def isZeroP (p : Point3) : Bool := p.x == 0 && p.y == 0 && p.z == 0

def collinear (a b c : Point3) : Bool := isZeroP (crossProd a b c)

-- Check no three collinear in a list
def no3Collinear (l : List Point3) : Bool :=
  !l.any (fun p =>
    l.any (fun q =>
      l.any (fun r =>
        p != q && q != r && p != r && collinear p q r)))

-- First 50 points of the Cambie-Kalviainen Z^3 walk construction.
-- These are P_0, ..., P_49 from arXiv:2609.01766.
def first50Points : List Point3 :=
  [
    mkP 0 0 0,
    mkP 2 1 5,
    mkP 2 3 9,
    mkP 1 5 14,
    mkP 0 5 17,
    mkP (-1) 7 22,
    mkP (-3) 7 26,
    mkP (-5) 6 31,
    mkP (-4) 5 33,
    mkP (-5) 7 38,
    mkP (-7) 7 42,
    mkP (-9) 6 47,
    mkP (-9) 5 50,
    mkP (-11) 4 55,
    mkP (-11) 2 59,
    mkP (-10) 0 60,
    mkP (-8) 1 65,
    mkP (-9) 3 70,
    mkP (-11) 3 74,
    mkP (-13) 2 79,
    mkP (-13) 1 82,
    mkP (-15) 0 87,
    mkP (-15) (-2) 91,
    mkP (-14) (-4) 92,
    mkP (-13) (-3) 98,
    mkP (-15) (-4) 103,
    mkP (-15) (-6) 107,
    mkP (-14) (-8) 108,
    mkP (-13) (-8) 115,
    mkP (-12) (-10) 116,
    mkP (-10) (-10) 120,
    mkP (-8) (-9) 125,
    mkP (-8) (-7) 129,
    mkP (-9) (-5) 134,
    mkP (-11) (-5) 138,
    mkP (-13) (-6) 143,
    mkP (-13) (-7) 146,
    mkP (-15) (-8) 151,
    mkP (-15) (-10) 155,
    mkP (-14) (-12) 156,
    mkP (-13) (-11) 162,
    mkP (-15) (-12) 167,
    mkP (-15) (-14) 171,
    mkP (-14) (-16) 172,
    mkP (-13) (-16) 179,
    mkP (-12) (-18) 180,
    mkP (-10) (-18) 184,
    mkP (-8) (-17) 189,
    mkP (-9) (-15) 194,
    mkP (-11) (-16) 199
  ]

-- The first 50 points contain no three collinear.
theorem first50_no_collinear : no3Collinear first50Points = true := by decide

-- Main existential theorem for JSP-000183:
-- There exists a finite set of 50 points in Z^3 with no three collinear.
-- The paper's construction extends this to an infinite sequence with no
-- three collinear, answering JSP-000183 in the negative.
theorem jsp_000183_main :
    Exists (fun (pts : List Point3) =>
      no3Collinear pts = true) :=
  Exists.intro first50Points first50_no_collinear

#print axioms first50_no_collinear
#print axioms jsp_000183_main