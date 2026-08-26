/-
# Gate 1A safe algebra bank — what deliberately remains UNFORMALIZED.

This file contains **no declarations at all**.  Each item below is an external
analytic or source obligation for Gate 1A.  Nothing in
`Gate1A.SafeAlgebra` asserts, assumes, or implies any of them.

Open Gate-1A interfaces (they already appear, uninhabited, as fields of
`Gate1A.Delta4.Delta4OpenInterfaces`, and are *not* proved anywhere):

* `flatProfileSourceLegality` — the identification of the source data with the
  flat profile.  First remaining unproved interface of the Δv4 development.
* `correctedPBAnalytic` — the corrected Poisson–Bruhat analytic lattice bound.
* `hZeroFirewallBound` — the `h = 0` firewall mass bound.
* `exceptionalSectorsBound` — the exceptional-table rows.
* `sourceCoherence` — the source-coherence input.

Prohibitions recorded for later research, none of which is a consequence of
anything in `Gate1A.SafeAlgebra`:

* The projective coordinate `Z L⁻¹ (mod R)` is **not** claimed to
  equidistribute; only the exact coordinate equivalence
  `R ∣ Dproj ↔ Z₁L₁⁻¹ ≡ Z₂L₂⁻¹ (mod R)` is banked.
* The four local prime-square conditions are **not** independent; see
  `Gate1B.local_conditions_not_independent`.
* The collision relation `Z₁L₂ = Z₂L₁` may **not** be replaced by the Cartesian
  product of its projections; see
  `Gate1A.SafeAlgebra.collision_relation_not_cartesian` and
  `Gate1A.SafeAlgebra.projective_sum_ne_cartesian_sum`.
* Grouping outer states by the **product** `Z·L` is not the collision relation;
  see the previously banked `Gate1A.Delta4.product_class_ne_ratio_class`.
* Character saturation on the projective coordinate is a tautology at every
  tensor power and yields no moment bound and no saving; see
  `Gate1A.SafeAlgebra.saturation_gives_no_value_information`.
* Gate-1A closure remains **conditional** on the five interfaces above; the
  only closure statement in the project is the explicitly conditional
  `Gate1A.Delta4.gate1a_of_final_interfaces`.
-/
