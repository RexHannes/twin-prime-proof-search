import RequestProject.NANC.Gate1BDet2.CommonShiftRigidity

/-!
# Gate 1B / determinant-2 bank, Module 34: composite-view geometry

The composite view of the determinant-2 relation writes the complementary
factor as a product `u ρ s`:

  `q l − u ρ s = 2`.                                (`CompositeDet2`)

Banked here, all exact and over `ℤ`:

* `composite_view_mod_u`, `composite_view_mod_s` — `q l ≡ 2 (mod u)` and
  `q l ≡ 2 (mod s)`;
* `det2_composite_view_mod_us` — under `IsCoprime u s`, CRT gives
  `q l ≡ 2 (mod u s)`;
* `composite_view_l_unique_in_short_interval` — interval uniqueness: two
  admissible `l` in an interval of diameter `< u s` coincide.  This *reuses*
  the residue-class rigidity of Module 22 (`ell_unique_in_short_interval`),
  which is not reproved;
* `composite_view_reconstructs_l_rho` — reconstruction: with `q, u, s, l` fixed
  and `u s ≠ 0`, `ρ` is the unique solution `ρ = (q l − 2) / (u s)`.

**No square-root gain, and no analytic statement, is claimed anywhere here.**
-/

namespace TwinPrimeProject
namespace Gate1BDet2
namespace Composite

/-- The composite-view determinant relation `q l − u ρ s = 2`. -/
def CompositeDet2 (q l u rho s : ℤ) : Prop := q * l - u * rho * s = 2

/-! ## 1. The two congruences and their CRT combination -/

/-- `q l ≡ 2 (mod u)`. -/
theorem composite_view_mod_u {q l u rho s : ℤ} (h : CompositeDet2 q l u rho s) :
    q * l ≡ 2 [ZMOD u] :=
  Int.modEq_iff_dvd.mpr ⟨-(rho * s), by unfold CompositeDet2 at h; linarith [h]⟩

/-- `q l ≡ 2 (mod s)`. -/
theorem composite_view_mod_s {q l u rho s : ℤ} (h : CompositeDet2 q l u rho s) :
    q * l ≡ 2 [ZMOD s] :=
  Int.modEq_iff_dvd.mpr ⟨-(u * rho), by unfold CompositeDet2 at h; linarith [h]⟩

/-- **`det2_composite_view_mod_us`.**  If `u` and `s` are coprime, the two
congruences combine (CRT) to `q l ≡ 2 (mod u s)`. -/
theorem det2_composite_view_mod_us {q l u rho s : ℤ} (hcop : IsCoprime u s)
    (h : CompositeDet2 q l u rho s) : q * l ≡ 2 [ZMOD u * s] := by
  unfold CompositeDet2 at h
  have hu : u ∣ q * l - 2 := ⟨rho * s, by linarith⟩
  have hs : s ∣ q * l - 2 := ⟨u * rho, by linarith⟩
  obtain ⟨c, hc⟩ := hcop.mul_dvd hu hs
  exact Int.modEq_iff_dvd.mpr ⟨-c, by linarith⟩

/-! ## 2. Interval uniqueness of `l` -/

/-- **Interval uniqueness.**  If `l₁, l₂` lie in an interval of diameter
`< u s`, both satisfy `q l ≡ 2 (mod u s)`, and `q` is invertible modulo `u s`,
then `l₁ = l₂`.

The rigidity step itself is Module 22's `ell_unique_in_short_interval`, reused
verbatim. -/
theorem composite_view_l_unique_in_short_interval {q u s l₁ l₂ : ℤ}
    (hus : 0 < u * s) (hcop : IsCoprime q (u * s))
    (h₁ : q * l₁ ≡ 2 [ZMOD u * s]) (h₂ : q * l₂ ≡ 2 [ZMOD u * s])
    (hshort : |l₁ - l₂| < u * s) : l₁ = l₂ :=
  ell_unique_in_short_interval hus hcop (by simpa [mul_comm] using h₁)
    (by simpa [mul_comm] using h₂) hshort

/-- The same statement directly on the composite view. -/
theorem composite_det2_l_unique_in_short_interval {q u s l₁ l₂ rho₁ rho₂ : ℤ}
    (hus : 0 < u * s) (hcop : IsCoprime q (u * s)) (hcopus : IsCoprime u s)
    (h₁ : CompositeDet2 q l₁ u rho₁ s) (h₂ : CompositeDet2 q l₂ u rho₂ s)
    (hshort : |l₁ - l₂| < u * s) : l₁ = l₂ :=
  composite_view_l_unique_in_short_interval hus hcop
    (det2_composite_view_mod_us hcopus h₁) (det2_composite_view_mod_us hcopus h₂) hshort

/-! ## 3. Reconstruction of `ρ` -/

/-- **`composite_view_reconstructs_l_rho` (existence half).**  Once `q, u, s, l`
are fixed with `u s ≠ 0` and `u s ∣ q l − 2`, the composite relation has a
solution `ρ = (q l − 2)/(u s)`. -/
theorem composite_view_rho_exists {q l u s : ℤ} (hus : u * s ≠ 0)
    (hdvd : u * s ∣ q * l - 2) : CompositeDet2 q l u ((q * l - 2) / (u * s)) s := by
  obtain ⟨c, hc⟩ := hdvd
  have hdiv : (q * l - 2) / (u * s) = c := by rw [hc]; exact Int.mul_ediv_cancel_left _ hus
  unfold CompositeDet2
  rw [hdiv]
  linarith [hc]

/-- **`composite_view_reconstructs_l_rho` (uniqueness half).**  With
`q, u, s, l` fixed and `u s ≠ 0`, the solution `ρ` is unique. -/
theorem composite_view_rho_unique {q l u s rho₁ rho₂ : ℤ} (hus : u * s ≠ 0)
    (h₁ : CompositeDet2 q l u rho₁ s) (h₂ : CompositeDet2 q l u rho₂ s) : rho₁ = rho₂ := by
  unfold CompositeDet2 at h₁ h₂
  have h : u * rho₁ * s = u * rho₂ * s := by linarith
  have h' : (u * s) * rho₁ = (u * s) * rho₂ := by ring_nf; ring_nf at h; linarith
  exact mul_left_cancel₀ hus h'

/-- **`composite_view_reconstructs_l_rho`.**  Full package: for fixed
`q, u, s, l` with `u s ≠ 0` and `u s ∣ q l − 2`, there is exactly one `ρ`, and
it is `(q l − 2)/(u s)`. -/
theorem composite_view_reconstructs_l_rho {q l u s : ℤ} (hus : u * s ≠ 0)
    (hdvd : u * s ∣ q * l - 2) :
    ∃! rho : ℤ, CompositeDet2 q l u rho s := by
  refine ⟨(q * l - 2) / (u * s), composite_view_rho_exists hus hdvd, ?_⟩
  intro y hy
  exact composite_view_rho_unique hus hy (composite_view_rho_exists hus hdvd)

end Composite
end Gate1BDet2
end TwinPrimeProject
