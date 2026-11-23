import Mathlib

/-! Integer cubature for the upper half of Gold 4.65 Part II (B4).
Coordinates are in units of 1/800. All operations in the certificate are natural arithmetic. -/
namespace REAL1B.FM.Grid

structure Coord where
  a : ℕ
  b : ℕ
  c : ℕ
  d : ℕ
  deriving DecidableEq, Repr

def Coord.atFin (p : Coord) : Fin 4 → ℕ := ![p.a, p.b, p.c, p.d]

def valid (p : Coord) : Bool :=
  let s := p.a+p.b+p.c+p.d
  decide (3 ≤ p.a ∧ p.a < p.b ∧ p.b < p.c ∧ p.c < p.d ∧ p.d ≤ 48 ∧ p.a+1 ≤ 19 ∧
    (p.a+1 ≤ 19 ∨ 21 ≤ p.a) ∧ (p.b+1 ≤ 19 ∨ 21 ≤ p.b) ∧
    (p.c+1 ≤ 19 ∨ 21 ≤ p.c) ∧ (p.d+1 ≤ 19 ∨ 21 ≤ p.d) ∧
    p.d+1+s ≤ 96 ∧ s+21 ≤ 96 ∧ 100 ≤ 49+s ∧ 51 ≤ p.a+p.c+p.d ∧ p.c+p.d+2 ≤ 49)

def atPair (d c : ℕ) : List Coord :=
  if c+d+2 ≤ 49 then (List.range c).flatMap fun b =>
    ((List.range b).map (fun a => Coord.mk a b c d)).filter valid
  else []

def bins := (List.range 49).flatMap fun d => (List.range d).flatMap (atPair d)

def subcells (p : Coord) := (List.range 8).flatMap fun i => (List.range 8).flatMap fun j =>
  (List.range 8).flatMap fun k => (List.range 8).map fun l =>
    Coord.mk (8*p.a+i) (8*p.b+j) (8*p.c+k) (8*p.d+l)

def faceCount (s : ℕ) : ℕ := (if 400 < s then 1 else 0) + (if 400 ≤ s then 1 else 0)
def height (m : Coord) := 2 + faceCount (m.a+m.b+m.d+3) + faceCount (m.a+m.b+m.c+3)
def den (m : Coord) := m.a*m.b*m.c*m.d*(800-(m.a+m.b+m.c+m.d))
def scale : ℕ := 10^20
def upperNumerator (m : Coord) := (height m * 800 * scale + den m - 1) / den m
def boxUpper (p : Coord) := ((subcells p).map upperNumerator).sum
def pairUpper (d c : ℕ) := ((atPair d c).map boxUpper).sum
def columnUpper (d : ℕ) := ((List.range d).map (pairUpper d)).sum
def totalUpper := ((List.range 49).map columnUpper).sum

/-- Fixed fanout keeps each numeral reduction small in the optional native certificate. -/
def sum8 (f : ℕ → ℕ) := f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7
def fastBox (p : Coord) := sum8 fun i => sum8 fun j => sum8 fun k => sum8 fun l =>
  upperNumerator ⟨8*p.a+i, 8*p.b+j, 8*p.c+k, 8*p.d+l⟩

private theorem sum8_spec (f : ℕ → ℕ) : ((List.range 8).map f).sum = sum8 f := by
  change f 0 + (f 1 + (f 2 + (f 3 + (f 4 + (f 5 + (f 6 + (f 7 + 0))))))) = _
  simp [sum8, Nat.add_assoc]

private theorem sum_map_flat {α β : Type*} (s : List α) (f : α → List β) (g : β → ℕ) :
    ((s.flatMap f).map g).sum = (s.map (fun x => ((f x).map g).sum)).sum := by
  induction s with
  | nil => rfl
  | cons _ _ ih => simp [ih]

theorem boxUpper_eq_fast (p : Coord) : boxUpper p = fastBox p := by
  simp only [boxUpper, subcells, sum_map_flat, List.map_map, Function.comp_def, sum8_spec, fastBox]

end REAL1B.FM.Grid
#print axioms REAL1B.FM.Grid.boxUpper_eq_fast
