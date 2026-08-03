import Mathlib

/-!
# Core Definitions for Reciprocal Subset-Sum Entropy

We formalize the basic objects appearing in the study of reciprocal subset-sum
collisions, relevant to Erdős Problem #319.

All sums are taken over `ℚ` for exactness.
-/

open scoped BigOperators
open Finset

noncomputable section

/-- The reciprocal sum `R(X) = ∑_{x ∈ X} 1/x` for a finset of positive naturals. -/
def recipSum (X : Finset ℕ+) : ℚ :=
  ∑ x ∈ X, (1 : ℚ) / (x : ℚ)

/-- The subset-sum image `Σ(Q) = {R(U) : U ⊆ Q}`. -/
def subsetSumImage (Q : Finset ℕ+) : Finset ℚ :=
  Q.powerset.image recipSum

/-- The number of subsets of `Q` mapping to value `t`. -/
def subsetSumMult (Q : Finset ℕ+) (t : ℚ) : ℕ :=
  (Q.powerset.filter (fun U => recipSum U = t)).card

/-- The collision count: number of ordered pairs (A,B) ⊆ Q with R(A) = R(B). -/
def collisionCount (Q : Finset ℕ+) : ℕ :=
  ((Q.powerset ×ˢ Q.powerset).filter (fun p => recipSum p.1 = recipSum p.2)).card

/-- A reciprocal identity (internal circuit) in Q: disjoint nonempty A, B ⊆ Q
    with R(A) = R(B). -/
structure ReciprocalIdentity (Q : Finset ℕ+) where
  A : Finset ℕ+
  B : Finset ℕ+
  hA_sub : A ⊆ Q
  hB_sub : B ⊆ Q
  hA_ne : A.Nonempty
  hB_ne : B.Nonempty
  hDisjoint : Disjoint A B
  hSum : recipSum A = recipSum B

/-- The support of a reciprocal identity. -/
def ReciprocalIdentity.support {Q : Finset ℕ+} (ri : ReciprocalIdentity Q) : ℕ :=
  ri.A.card + ri.B.card

/-- Clearing denominators: the integer weight of element q with respect to L. -/
def intWeight (L q : ℕ+) : ℕ := (L : ℕ) / (q : ℕ)

end
