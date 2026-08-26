/-
# Gate-1A §17: source-interface definitions — **no axioms**

Everything in this file is a `Prop`-valued `structure`.  Nothing here is an
`axiom`, a `constant`, or a `sorry`.  A term of one of these structures is
never constructed in this project: the structures exist so that downstream
theorems can take them as *explicit hypotheses*.

The mathematical status they encode is:

    GATE1A_DIRECT_GENERIC_OPEN

Each field is a genuine, non-vacuous assertion about the abstract Gate-1A
packet.  None of them is proved here.
-/
import Mathlib
import Gate1A.Exponents

namespace Gate1A

namespace SourceInterfaces

/-! ## The abstract finite Gate-1A packet

`X^{o(1)}` is **not** encoded as magic: all scales are explicit positive real
parameters. -/

/-- The abstract finite Gate-1A packet: explicit positive parameters, no
asymptotic notation. -/
structure Gate1APacket where
  /-- moving family size `S`. -/
  S : ℝ
  /-- pairwise collision codegree `D`. -/
  D : ℝ
  /-- conservative *natural* (`ℓ¹`) scale `B_nat`. -/
  Bnat : ℝ
  /-- diagonal / projective (`ℓ²`) scale `B_diag`.  Never identified with
  `B_nat`: see `Gate1A/NuclearCountermodels.lean`. -/
  Bdiag : ℝ
  /-- factor multiplicity `τ`. -/
  tau : ℝ
  /-- recombination *amplitude* error `ε`. -/
  eps : ℝ
  /-- required variance saving `δ` (`= H/M` in the frozen ledger). -/
  delta : ℝ
  /-- the normalised target. -/
  target : ℝ
  hS : 0 < S
  hD : 0 ≤ D
  htau : 0 ≤ tau
  hBnat : 0 ≤ Bnat
  hBdiag : 0 ≤ Bdiag
  heps : 0 ≤ eps
  hdelta : 0 ≤ delta

/-- The normalised variance of the packet: curvature branch, projective
branch, recombination error branch. -/
def normalizedVariance (curv proj err : ℝ) : ℝ := curv + proj + err

/-- The normalised Gate-1A target. -/
def Gate1ANormalizedTarget (P : Gate1APacket) (v : ℝ) : Prop := v ≤ P.target

/-! ## §17: the source interfaces (all OPEN) -/

/-- **`Gate1ASourceInterfaces`** — the exact source assertions that remain
mathematically open.  These are hypotheses, never assumptions discharged in
this project.

* `postNuLiteral` — the literal post-`ν` coefficient of the authoritative
  pre-square source has nuclear `ℓ¹` mass `nuc` obeying the Gate
  normalisation `S · nuc² ≤ B_nat`.  (This is exactly the normalisation
  hypothesis of the *proved* theorem `normed_transported_curvature`.)
* `side2CoordinateDictionary` — the curvature branch is genuinely routed
  through the kernel-checked **negative** side-2 cross formula
  (`cross_q_side2_negative`), giving the transported bound with the literal
  nuclear mass.
* `phiFlatCensus` — every remaining factor is accounted for as exact source
  phase / Schwartz weight / dyadic selector / local projection / exceptional
  sector term, and the total is the recorded amplitude error.
* `transformOrder` — quotient recombination and the all-mode `t/ν` transforms
  are applied in a source-preserving order: the two orders agree exactly.
* `normedTransport` — the Gate-normalised transport bound for the actual
  source (not a schematic common-envelope statement; see the countermodel
  `uniform_row_smoothness_not_nuclear_transport`).
* `projectivePushforward` — the actual source row/graph nuclear decomposition
  with *diagonal-scale* nuclear norm.
* `rankLossRouting` — literal routing of the `r`-local true zero vector and
  the proper-conductor sectors, in the recombined dimension.
* `recombinedDomain` — the exact finite recombined source-domain size.
  `N_old ≈ 2L²U` may **not** be reused after quotient recombination. -/
structure Gate1ASourceInterfaces (P : Gate1APacket)
    (curv proj err nuc Ndiag Nnew trAsq Dr Hscale orderA orderB : ℝ) : Prop where
  postNuLiteral : P.S * nuc ^ 2 ≤ P.Bnat
  side2CoordinateDictionary : curv ≤ (P.D / P.S) * (P.S * nuc ^ 2)
  phiFlatCensus : err ≤ P.eps ^ 2 * P.Bnat
  transformOrder : orderA = orderB
  normedTransport : curv ≤ (P.D / P.S) * P.Bnat
  projectivePushforward : proj ≤ P.tau * Ndiag
  rankLossRouting : trAsq / Nnew ≤ Dr / Hscale
  recombinedDomain : Nnew = 2 * P.Bdiag ∧ Ndiag = P.Bdiag

/-- **`Gate1AAnalyticInterfaces`** — the analytic inputs that are not derived
in this project.

* `pbSchwartzLatticeL1` — the 2D Poisson–Bruhat lattice `ℓ¹` bound for the
  actual sheared source lattice (naive box counting is **not** sufficient).
* `pbPrefactorTimesLatticeL1` — the prefactor-weighted version.
* `pbSourceOperatorBound` — the *operator* bound; by the countermodel
  `scalar_l1_mass_not_operator_norm` this is strictly stronger than the
  scalar `ℓ¹` mass bound and must be supplied separately.
* `thetaPhaseTailAdmissible` — the retained theta phase's separated tail is
  below the amplitude error (the abstract tail estimate itself is *proved* in
  `Gate1A/ThetaPhase.lean`; what is open is that the source's parameters lie
  in its range). -/
structure Gate1AAnalyticInterfaces (P : Gate1APacket)
    (latticeL1 prefactor opBound thetaTail : ℝ) : Prop where
  pbSchwartzLatticeL1 : latticeL1 ≤ P.Bnat
  pbPrefactorTimesLatticeL1 : prefactor * latticeL1 ≤ P.Bnat
  pbSourceOperatorBound : opBound ≤ P.Bdiag
  thetaPhaseTailAdmissible : thetaTail ≤ P.eps

/-! ## The addendum's S1 / S2 / S3 decomposition -/

/-- **S1 (A8): the five-face intertwiner branch.**  Supplies the curvature
(nonzero-curvature) energy from the literal source nuclear mass.
`faceMinorNonRedundant` (A16) records that the five faces are not redundant:
the minor's rank floor is genuinely attained. -/
structure S1FiveFaceIntertwiner (P : Gate1APacket) (curv nuc minorRank : ℝ) :
    Prop where
  nuclearNormalisation : P.S * nuc ^ 2 ≤ P.Bnat
  curvatureTransport : curv ≤ (P.D / P.S) * (P.S * nuc ^ 2)
  faceMinorNonRedundant : 0 < minorRank

/-- **S2 (A11): the TF4 normalisation chain.**  Supplies the recombination
error branch, together with the root-depth condition `ε ≤ √δ` that
`error_absorbed_of_le_sqrtSaving` requires. -/
structure S2TF4Normalisation (P : Gate1APacket) (err : ℝ) : Prop where
  amplitudeError : err ≤ P.eps ^ 2 * P.Bnat
  rootDepth : P.eps ≤ Real.sqrt P.delta

/-- **S3 (A15): the actual projective source pushforward.**  Supplies the
projective branch at the *diagonal* scale. -/
structure S3ProjectivePushforward (P : Gate1APacket) (proj Ndiag : ℝ) : Prop where
  nuclearDiagonalScale : Ndiag ≤ P.Bdiag
  projectiveEnergy : proj ≤ P.tau * Ndiag

/-! ## The numerical margins -/

/-- The purely numerical inequalities that place all three branches below the
target.  These are *not* open: they are conditions on the packet's explicit
parameters, and are discharged by arithmetic at any concrete instantiation. -/
structure Gate1ANumericalMargins (P : Gate1APacket) : Prop where
  curvatureMargin : (P.D / P.S) * P.Bnat ≤ P.target / 3
  projectiveMargin : P.tau * P.Bdiag ≤ P.target / 3
  errorMargin : P.eps ^ 2 * P.Bnat ≤ P.target / 3

end SourceInterfaces

end Gate1A
