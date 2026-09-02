/-
# Universal / D0WP — ULTRA → `d0·wp` provider interface and the ultra compilers

**Status of this module: CONDITIONAL_KERNEL; the provider pin is UNINHABITED.**

§19.  `UltraToPhysicalQProviderPin` asserts *exactly* that, after freezing all
outer HB data, the remaining inner source of an ultra row is the same `d0 · wp`
provider source: identical inner source record, identical separation data,
identical centering data, identical Perron ledger data, and a frozen-outer
factorisation of the packet.  It is not inhabited here and must not be inhabited
automatically.

§20.  The `ThetaCut` and `ThetaCross` compilers are finite: conditional on the
provider bound and the pin, the ultra sums obey the corresponding bounds.

Recorded architecture fact: **cross-block prime-pair dispersion is NOT REQUIRED**
by this architecture.  This is a statement about what the compilers use, not a
claim that prime-pair dispersion is false.
-/
import Universal.D0WP.SourcePins
import Universal.D0WP.PerronLedger
import Universal.D0WP.UltraSourceSplit
import Universal.D0WP.FinitePacketCompiler

namespace Universal.D0WP

open Finset

/-- The inner data of an ultra (or provider) family. -/
structure UltraProviderData (ι : Type*) where
  /-- The inner `d0 · wp` source. -/
  inner : ι → D0WPSource
  /-- The separation data. -/
  sep : SeparationData ι
  /-- The centering data. -/
  centering : ι → CenteringData
  /-- The Perron / nuclear data. -/
  perron : ι → PerronSourceData
  /-- The packet value. -/
  packet : ι → ℂ

/-- **SOURCE PIN (UNINHABITED here).**  After freezing the outer HB data
(`outer`), the ultra family's inner source is literally the `d0 · wp` provider
source. -/
structure UltraToPhysicalQProviderPin {ι : Type*}
    (ultra provider : UltraProviderData ι) (outer : ι → ℂ) : Prop where
  /-- Same `D, W` source ranges, because the inner source record is the same. -/
  sameInner : ∀ i, ultra.inner i = provider.inner i
  /-- Same `d0`/`wp` separation. -/
  sameSep : ultra.sep = provider.sep
  /-- Same centering. -/
  sameCentering : ∀ i, ultra.centering i = provider.centering i
  /-- Same Perron ledger. -/
  samePerron : ∀ i, ultra.perron i = provider.perron i
  /-- Frozen-outer factorisation of the ultra packet. -/
  frozenFactorisation : ∀ i, ultra.packet i = outer i * provider.packet i

/-- **Ultra covariance bound, conditional on the provider input and the pin
(kernel-proved implication).** -/
theorem ultra_covariance_of_provider {ι : Type*}
    {ultra provider : UltraProviderData ι} {outer : ι → ℂ}
    (pin : UltraToPhysicalQProviderPin ultra provider outer)
    (s : Finset ι) {Cout B : ℝ} (hCout : 0 ≤ Cout)
    (houter : ∀ i ∈ s, ‖outer i‖ ≤ Cout)
    (hprov : ∀ i ∈ s, ‖provider.packet i‖ ≤ B) :
    ‖∑ i ∈ s, ultra.packet i‖ ≤ (s.card : ℝ) * (Cout * B) := by
  refine finite_packet_bound s ultra.packet (Cout * B) ?_
  intro i hi
  rw [pin.frozenFactorisation i, norm_mul]
  exact mul_le_mul (houter i hi) (hprov i hi) (norm_nonneg _) hCout

/-- **ThetaCut compiler (kernel-proved implication).**  The same-block cut rows
are handled term by term by the same provider — no HB sibling cancellation is
invoked. -/
theorem thetaCut_compiler {ι : Type*} [DecidableEq ι]
    {ultra provider : UltraProviderData ι} {outer : ι → ℂ}
    (pin : UltraToPhysicalQProviderPin ultra provider outer)
    (blocks : UltraBlockData ι) (Θ : Finset ι) {Cout B : ℝ}
    (hCout : 0 ≤ Cout)
    (houter : ∀ i ∈ ThetaCut blocks Θ, ‖outer i‖ ≤ Cout)
    (hprov : ∀ i ∈ ThetaCut blocks Θ, ‖provider.packet i‖ ≤ B) :
    ‖∑ i ∈ ThetaCut blocks Θ, ultra.packet i‖
      ≤ ((ThetaCut blocks Θ).card : ℝ) * (Cout * B) :=
  ultra_covariance_of_provider pin _ hCout houter hprov

/-- **ThetaCross compiler (kernel-proved implication).**  With the outer primes
`p₁, p₂` frozen, cross-block rows are handled by the same provider; no
cross-block prime-pair dispersion input is used. -/
theorem thetaCross_compiler {ι : Type*} [DecidableEq ι]
    {ultra provider : UltraProviderData ι} {outer : ι → ℂ}
    (pin : UltraToPhysicalQProviderPin ultra provider outer)
    (blocks : UltraBlockData ι) (Θ : Finset ι) {Cout B : ℝ}
    (hCout : 0 ≤ Cout)
    (houter : ∀ i ∈ ThetaCross blocks Θ, ‖outer i‖ ≤ Cout)
    (hprov : ∀ i ∈ ThetaCross blocks Θ, ‖provider.packet i‖ ≤ B) :
    ‖∑ i ∈ ThetaCross blocks Θ, ultra.packet i‖
      ≤ ((ThetaCross blocks Θ).card : ℝ) * (Cout * B) :=
  ultra_covariance_of_provider pin _ hCout houter hprov

/-- **Assembled ultra bound (kernel-proved implication).**  Cross plus cut
exhausts the ultra family, so the two compilers assemble without overlap. -/
theorem ultra_total_of_split {ι : Type*} [DecidableEq ι]
    {ultra provider : UltraProviderData ι} {outer : ι → ℂ}
    (pin : UltraToPhysicalQProviderPin ultra provider outer)
    (Θ : Finset ι) {Cout B : ℝ}
    (hCout : 0 ≤ Cout)
    (houter : ∀ i ∈ Θ, ‖outer i‖ ≤ Cout)
    (hprov : ∀ i ∈ Θ, ‖provider.packet i‖ ≤ B) :
    ‖∑ i ∈ Θ, ultra.packet i‖ ≤ (Θ.card : ℝ) * (Cout * B) :=
  ultra_covariance_of_provider pin Θ hCout houter hprov

/-- The provider pin is a genuine obligation: it can fail. -/
theorem ultraProviderPin_not_automatic :
    ∃ (ultra provider : UltraProviderData Unit) (outer : Unit → ℂ),
      ¬ UltraToPhysicalQProviderPin ultra provider outer := by
  classical
  let src : D0WPSource := ⟨1, 2, 3, 4, 1, 1, 1⟩
  let sep : SeparationData Unit := ⟨fun _ => 1, fun _ => 1, fun _ => 1, fun _ => 1, fun _ => 1⟩
  refine ⟨⟨fun _ => src, sep, fun _ => ⟨0, 0⟩, fun _ => ⟨1, 1, 0, fun _ => 0⟩, fun _ => 1⟩,
    ⟨fun _ => src, sep, fun _ => ⟨0, 0⟩, fun _ => ⟨1, 1, 0, fun _ => 0⟩, fun _ => 0⟩,
    fun _ => 1, ?_⟩
  intro pin
  have := pin.frozenFactorisation ()
  norm_num at this

end Universal.D0WP
