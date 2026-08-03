import RequestProject.NANC.D4.Prop44Assignments

namespace NANC.D4

private def cell (η : ℚ) (P : Prop) (u v l : ℚ) := HighP3Atomic η u v l ∧ P

def Cell123j1 (η ε u v l : ℚ) := cell η (u ≤ 1/9-ε ∧ v+2*l ≤ 7/9-15*ε ∧ 5*v+2*l ≤ 16/9-40*ε) u v l
def Cell213j1 (η ε u v l : ℚ) := cell η (v ≤ 1/9-ε ∧ u+2*l ≤ 7/9-15*ε ∧ 5*u+2*l ≤ 16/9-40*ε) u v l
def Cell132j1 (η ε u v l : ℚ) := cell η (u ≤ 1/9-ε ∧ l+2*v ≤ 7/9-15*ε ∧ 5*l+2*v ≤ 16/9-40*ε) u v l
def Cell312j1 (η ε u v l : ℚ) := cell η (v ≤ 1/9-ε ∧ l+2*u ≤ 7/9-15*ε ∧ 5*l+2*u ≤ 16/9-40*ε) u v l
def Cell132j2 (η ε u v l : ℚ) := cell η (u ≤ 2/9-ε ∧ l+2*v ≤ 5/9-15*ε ∧ 5*l+2*v ≤ 14/9-40*ε) u v l
def Cell312j2 (η ε u v l : ℚ) := cell η (v ≤ 2/9-ε ∧ l+2*u ≤ 5/9-15*ε ∧ 5*l+2*u ≤ 14/9-40*ε) u v l
def Cell121j3 (η ε u v l : ℚ) := cell η (u+l ≤ 1/3-ε ∧ v ≤ 1/3-15*ε ∧ 5*v ≤ 4/3-40*ε) u v l
def Cell211j3 (η ε u v l : ℚ) := cell η (v+l ≤ 1/3-ε ∧ u ≤ 1/3-15*ε ∧ 5*u ≤ 4/3-40*ε) u v l
def Cell231j3 (η ε u v l : ℚ) := cell η (l ≤ 1/3-ε ∧ u+2*v ≤ 1/3-15*ε ∧ 5*u+2*v ≤ 4/3-40*ε) u v l
def Cell321j3 (η ε u v l : ℚ) := cell η (l ≤ 1/3-ε ∧ v+2*u ≤ 1/3-15*ε ∧ 5*v+2*u ≤ 4/3-40*ε) u v l
def Cell121j4 (η ε u v l : ℚ) := cell η (u+l ≤ 4/9-ε ∧ v ≤ 1/9-15*ε ∧ 5*v ≤ 10/9-40*ε) u v l
def Cell211j4 (η ε u v l : ℚ) := cell η (v+l ≤ 4/9-ε ∧ u ≤ 1/9-15*ε ∧ 5*u ≤ 10/9-40*ε) u v l

def RouteBClosed12 (η ε u v l : ℚ) : Prop :=
  Cell123j1 η ε u v l ∨ Cell213j1 η ε u v l ∨
  Cell132j1 η ε u v l ∨ Cell312j1 η ε u v l ∨
  Cell132j2 η ε u v l ∨ Cell312j2 η ε u v l ∨
  Cell121j3 η ε u v l ∨ Cell211j3 η ε u v l ∨
  Cell231j3 η ε u v l ∨ Cell321j3 η ε u v l ∨
  Cell121j4 η ε u v l ∨ Cell211j4 η ε u v l

private def aa (u v l : Prop44Slot) : AtomicAssignment := ⟨u,v,l⟩

/- The complete 216-branch classification theorem is the first open declaration. -/

end NANC.D4
