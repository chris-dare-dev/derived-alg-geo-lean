# Projective-family construction and surface stability: bridge contract

**Snapshot:** 2026-09-08 (America/New_York)
**Kind:** source-faithful contract for WP0. This is not a theorem, a coverage
record, or a construction of a stability condition.

This note freezes the comparison target between the projective-embedding
construction of Li--Liu--Liu--Macrì--Perry--Stellari--Zhao and the classical
surface construction reviewed by Macrì--Schmidt. The contract is deliberately
stronger than a list of TODOs and weaker than an equality of stability
conditions: every numerical, heart, support, and component comparison that is
not present in the repository is named as an input.

## Pinned sources and source corrections

The primary projective-family artifact is [arXiv:2607.28411v1](https://arxiv.org/abs/2607.28411),
submitted 2026-07-30. The repository pins its PDF by
`f8770154235fe2c82698513b4633b3ee509fa11f722190a4c9f573fca589a98c`; the same
pin is recorded in `registry/coverage-2607.28411.json` and
`.claude/roadmap/projective-families.yaml`.

The relevant source locations in that v1 artifact are:

* Example 6.1 (`ex:SmoothAbelianGroup`), which compares the embedding image
  lattice with the coordinates built from `ch · td_X` by
  Hirzebruch--Riemann--Roch;
* Theorem 6.2 (`thm:ProjectiveScheme`), the large-`a` projective-scheme
  pullback;
* Remark 6.3 (`rmk:CompatibilityEn`), the warning that the pulled-back charge
  is generally not `-∫ exp(-(b + i a) H_X) ch`;
* Definition 6.4 (`def:StabdaggerAbsolute`), the embedding-indexed lattice and
  distinguished component;
* Lemma 6.5 (`lem:Numerical Data Equal`) and the following Theorem 6.8,
  embedding independence of the numerical data and component;
* Proposition 7.6 (`prop:MassHomBoundSurfaces`), the mass-Hom bound for
  surfaces. The surface comparison itself is the paragraph preceding it in
  Section 7.2: for a geometric condition in the distinguished component,
  the source cites Dell, *Stability conditions on free abelian quotients*
  (Épijournal Géom. Algébrique 9 (2025), art. 16), Theorem 5.10 for the
  `GL⁺₂(ℝ)`-classification of geometric conditions, Proposition 5.35 for
  the full support property with respect to `K_num(X)`, and Theorem 5.36
  for connectedness of the geometric conditions. None of these is proved in
  the projective-family paper; Dell is the owner of that classification.

The handoff's labels “Theorem 6.8”, “Proposition 7.6”, and “Theorem 10.3”
refer to the numbered results in the full v1 PDF. The arXiv HTML conversion
currently stops partway through Section 6, so its visible headings do not
display every later numbered result. The PDF/TeX v1 artifact, not the partial
HTML rendering, is authoritative.

The surface reference is [Macrì--Schmidt,
*Lectures on Bridgeland Stability*, arXiv:1607.01262v3](https://arxiv.org/abs/1607.01262).
Its Section 6 gives the HRS tilt and the surface charge; the primary results
behind that exposition are Bridgeland's K3 construction and Arcara--Bertram's
surface construction. The repository's `registry/coverage-1607.01262.json`
is a zero-claim map and does not promote any of those references to coverage.

## Frozen notation and normalizations

Throughout this note:

* `X` is a smooth projective surface over `ℂ`.
* `ι : X ↪ Pⁿ` is a closed embedding, and
  `H = c₁(ι* O_{Pⁿ}(1))`. If a fixed ample class is written `H_X`, the
  embedding-independence theorem assumes `H = m H_X` for some `m > 0`.
* Li's parameters are `(a,b) ∈ ℝ_{>0} × ℝ`, with `a` above the threshold
  determined by the embedding data. They are not globally identified merely
  by notation with the surface parameters below; the `P²` specialization is
  computed explicitly later in this section.
* The projective-space charge is
  `Z_{Pⁿ}^{a,b} = -∫_{Pⁿ} exp(-(b + i a) H_{Pⁿ}) ch`.
  The pulled-back charge is the projective-space charge evaluated on the
  pushforward class, through the image lattice `Λ_ι`.
* Li's class map is
  `v_ι : K₀(X) → Λ_ι`, where
  `Λ_ι = image(K₀(X) → K₀(Pⁿ) → K_num(Pⁿ))`.
  For a smooth geometrically integral `d`-fold, Example 6.1 identifies this,
  up to an automorphism supplied by HRR, with
  `(H^s (ch · td_X)_{d-s})_{0 ≤ s ≤ d}`. On a surface this has three slots.
  This is `td_X`, not `sqrt(td_X)`.
* Macrì--Schmidt use `ch^B = exp(-B) ch` and explicitly expand the surface
  charge as
  `Z_{ω,B}(E) = (-ch₂^B(E) + (ω²/2) ch₀^B(E))
  + i (ω · ch₁^B(E))`.
  This expanded formula is `-∫_X exp(-iω) ch^B`, hence
  `-∫_X exp(-B - iω) ch`. Their preceding display writes `exp(iω)`, whose
  literal expansion would have the opposite sign in the imaginary part; the
  explicit real/imaginary formula and the upper-half-plane convention fix the
  intended sign used by this contract.
* Consequently, on `P²` with its standard hyperplane class and the identity
  embedding, Li's parameters specialize to the standard surface parameters by
  the identity map `(a,b) ↦ (ω,B) = (aH,bH)`. The two central charges are
  equal, not complex conjugate. The identity embedding is the only case in
  which no Todd correction appears: for any other embedding with
  `H = mH_X`, the exponential factor alone rescales the scalar coordinates
  relative to `H_X` to `(ma,mb)`, but by Remark 6.3 the pulled-back charge
  is then *not* `-∫ exp(-(mb + i ma) H_X) ch`; the GRR/Todd term of C1–C2
  must be computed first.
* The standard heart is
  `Coh^{ω,B}(X) = ⟨F_{ω,B}[1], T_{ω,B}⟩`, where the torsion pair is cut at
  `μ_{ω,B} = 0`. The surface parameters allow arbitrary ample
  `ω ∈ Amp(X)_ℝ` and `B ∈ N¹(X)_ℝ`.
* A skyscraper sheaf has charge `-1` in the displayed surface convention, so
  its normalized phase is `1`. Li's large-`a` pullback is also geometric with
  skyscraper phase `1` by Theorem 6.2. This common behavior is a required
  comparison datum, not a heart-identification theorem.

## The contract

The following are the obligations of a future Lean package. A field described
as “supplied” is not a disguised theorem: it marks the exact geometric or
analytic result that must later be proved by a different layer.

### C1. Numerical lattice and Todd comparison

For a chosen numerical class carrier `N`, a Li lattice `Λ_ι`, and a surface
lattice `Λ_surf`, supply:

1. additive class maps `vLi : K₀(X) → Λ_ι` and
   `vSurface : K₀(X) → Λ_surf`;
2. a rank-three image statement for `Λ_ι` in the smooth surface case;
3. an additive lattice equivalence (or an explicitly stated quotient/map)
   `u : Λ_ι ≃ Λ_surf` with `u (vLi x) = vSurface x`;
4. the HRR/Todd coordinate specification of `vSurface`, using the three
   coordinates `(H^s (ch · td_X)_{2-s})_{0 ≤ s ≤ 2}` or another explicitly
   named upper-triangular normalization;
5. the hypotheses making the comparison numerical: smoothness, properness,
   the embedding class, and the GRR statement used to identify pushforward
   coordinates, namely `ch(ι_* E) · td(Pⁿ) = ι_*(ch(E) · td_X)`, so that the
   pushforward class is read through `td(Pⁿ)^{-1}` as well as `td_X`;
6. the factorization of `v_ι` through `K_num(X)` (used in the proof of
   Lemma 6.5 through `K_num(D_perf(X))`).

`Λ_surf` must be chosen deliberately. In Picard rank one it can be the full
three-coordinate surface numerical lattice. In higher Picard rank the Li
construction is only the `H`-slice/image detected by the projective Hilbert
polynomial; it is not automatically the full `K_num(X)` lattice used by the
most general surface stability condition. A comparison to full `K_num(X)`
therefore needs an additional inclusion, quotient, or factorization statement.

No canonical equivalence is asserted for an arbitrary singular scheme.

### C2. Central-charge comparison

After C1, supply the actual coordinate calculation, for every parameter in the
common domain, in one of the following forms:

```text
ZLi(a,b) = Zsurface(α(a,b), β(a,b)) ∘ u
```

or

```text
ZLi(a,b) = g • (Zsurface(α(a,b), β(a,b)) ∘ u)
```

for an explicitly named orientation-preserving real linear transformation
`g` and its phase action. The calculation must specify the meanings of
`α`, `β`, `ω`, and `B`; it may not silently set `a = α` and `b = β`.

The `td_X` correction in C1 is part of this calculation. The raw pulled-back
Li charge is not to be rewritten as the untwisted surface exponential charge
until the Todd factor has been computed and absorbed by a proved coordinate
change or by `g`. The first test cases are `P²`, `P¹ × P¹` with the Segre
polarization, and a Picard-rank-one K3 numerical model.

What the landed `P²` adapter proves, exactly: the arithmetic identity
`-∫ exp(-(b + i a)H) ch = Z_{aH,bH}` on a placeholder integral carrier
`(r,c,v)` that is coordinate-for-coordinate the existing `SurfaceNum`
presentation (`ch₂ = c/2 + v` on both sides), under the identity map of
coordinates. It does **not** define Li's `Λ_ι` or `v_ι`, does not compare two
different lattices, and does not compare stability conditions, hearts, or
slicings. The general identity behind it is
`Surface.ChargeCoordinates.centralCharge_twistByScalar_apply`, which holds on
every polarised surface. The `P²`-specific content is only that `H² = 1`
makes the compressed and full first Chern class coincide.

Li's parameter domain is `a > a₀`, with `a₀` depending on the Hilbert
polynomial of the embedding (Theorem 6.2). No Lean parameter space in the
repository records this threshold; every comparison statement is therefore
about the full `(a,b)` plane and must be restricted to Li's domain before it
is read as a statement about Li's stability conditions.

### C3. Heart and slicing comparison

The standard surface heart, charge, and Bogomolov support package is one
standalone geometric target. Li's construction supplies instead the preimage
slicing

```text
P̃_X(φ) = { E | ι_* E ∈ P_{Pⁿ}(φ) }.
```

The contract must not contain the unproved assertion
`P̃_X((0,1]) = Coh^{ω,B}(X)`. A stronger equality requires both the charge
comparison in C2 and a theorem comparing the two slicings/hearts. Until then,
the honest comparison datum is one of:

* a proved equality of hearts and a proved equality of slicings in a restricted
  case; or
* two stability conditions with separately supplied compatible class maps,
  normalized charges, geometric skyscraper phases, and a path in the
  stability manifold.

The surface weak-slope input must use the repository's
`WeakSlopeData`/weak-heart route. Its closed upper half-plane is essential:
skyscraper sheaves can have zero rank and zero degree. The strict curve
`SlopeData` API is not a substitute.

### C4. Support and Bogomolov comparison

Supply the common numerical support statement needed to compare the two
conditions. On the standard side this is the classical Bogomolov inequality
for slope-semistable torsion-free sheaves, followed by the HRS construction
and the surface support inequality. The repository currently records these
geometric inequalities as `BogomolovGiesekerData` and
`HodgeIndexStatement`; it does not turn them into universal facts about an
arbitrary abelian category.

On the Li side, supply the support form for the pulled-back condition and the
comparison of that form with the surface form under C1/C2. Geometricity alone
does not identify support forms or connected components.

Two numerical obligations that sat between the landed divisorial layer and
this comparison are now stated in `Numerical/Stability/DivisorialDiscriminant.lean`:

* the Macrì--Schmidt forms in the full divisor space: `ChernCharacter.discriminant`
  (`Δ = (ch₁)² - 2 ch₀ ch₂`, proved `B`-invariant), `barDiscriminant`
  (`ar Δ^B_ω`), and `discriminantC` (`Δ^C_{ω,B}`) of Definition 6.12, with
  `ω² Δ ≤ ar Δ^B_ω` under a Hodge index at `ω` and the identification of the
  bar form on the rank-one slice with `α² · discrH`, hence with the wall-plane
  discriminant of the transported class;
* the Hodge bridge: `DivisorSpace.HodgeIndex S H` is the real-divisor-space
  certificate; it yields the numerical `HodgeIndexStatement`, while the
  numerical statement yields only the inequality on realized first Chern
  classes. `OrthogonalSlice.isHodge_of_hodgeIndex` derives the slice
  certificate from the inequality plus nondegeneracy of the transverse
  pairing; the rank-one slice is Hodge from `H² > 0` alone.

What remains supplied, not proved: the Hodge index theorem itself for a
geometric surface, Bogomolov's inequality (`BogomolovGiesekerData`), and the
Bridgeland-semistable half of Theorem 6.13.

Separately, `Wall.ChargeFamily.wall v w` is the proportionality locus of the
two charges and is all of the parameter space when `w ∈ ℤ v` or `Z(v) = 0`
(`wall_self`, `wallValue_zsmul_right`). An *actual* wall additionally needs
semistable objects with those classes on it (Macrì--Schmidt Proposition
6.22(7)); that comparison is a stability-condition obligation, not a
numerical one.

### C5. Distinguished component

For fixed `H_X`, supply or prove the following path statement:

```text
the large-a Li condition for an embedding with c₁(O_X(1)) = m H_X
and the normalized standard surface condition lie in the same connected
component of the chosen numerical stability space.
```

The Li source gives embedding-independence of its distinguished component and
the large-parameter construction. The paragraph before Proposition 7.6 places
the relevant geometric surface conditions in the numerical distinguished
component, using Dell's classification of geometric surface conditions up to
the `GL⁺(2,ℝ)`-cover action (Dell, Theorem 5.10, Propositions 5.15 and 5.35,
Theorem 5.36; see the source list above). The repository's existing
deformation/component APIs can consume such a path, but they do not construct
this geometric path, and the repository does not yet cite or pin Dell.

For Picard rank one, the direct parameter comparison is the first target:
write `ω = αH` and `B = βH` only after C2 fixes the coordinate map. For higher
Picard rank, the result must be stated as a component/deformation statement
from the Li `H`-slice to a desired `(ω,B)`; the two Li parameters do not
parametrize all of `Amp(X)_ℝ × N¹(X)_ℝ`.

## Existing repository dependencies and boundaries

| Bridge obligation | Existing substrate | Still missing |
|---|---|---|
| HRR/Todd coordinates | `AlgebraicGeometry.Numerical`, `RiemannRoch/Surface`, `Numerical/Mukai/SqrtTodd` | the geometric `K₀(X)` pushforward image and GRR equivalence with `Λ_ι` |
| surface charge arithmetic | `Numerical/Stability/TwistedChern`, `SurfaceCharge`, `SurfaceChargeNumerical`, `DivisorialCharge`, `DivisorialChargeNumerical`, `Examples/Surface/ProjectivePlaneCharge`, `Examples/Surface/SmoothQuadric{,Charge}` | the geometric Li image lattice and its pullback realization; extension from rational to arbitrary real ring-level `B` classes beyond the intrinsic divisor-space API |
| BG/support input | `Numerical/Stability/BogomolovGieseker`, weak support APIs | geometric semistability, HRS realization on `Coh(X)`, and comparison of support forms |
| HRS/weak heart | `StabilityCondition/Weak/Tilting`, `WeakSlopeData`, `HnTiltHeart` | the geometric `Coh^{ω,B}(X)` instance and its charge/HN proof |
| categorical transfer | `Phase/Transfer`, `Polishchuk`, bounded-coherent pushforward/base change | scheme-specific `Dqc` inputs, conservativity, finite-Tor/resolution witnesses |
| component/deformation | `StabilityCondition/Foundation/Deformation`, phase and `GL~⁺₂` APIs | a geometric path or a source theorem identifying the two endpoints |
| relative family | `Families/Ordinary`, `CategoricalOrdinary`, relative numerical work in #851 | relative HN, S-locality, base change, boundedness, and the family class-map comparison |

The Li descent ledger in #217 and the transfer work in #1033 remain separate
dependencies. This lane must not add a second generic transfer carrier. The
relative family bridge waits for the absolute C1--C5 comparison and for the
relative numerical class-map work.

## Landed arithmetic boundary

The arithmetic boundary is split across composable components:

* `StabilityCondition/Walls/ChargeFamily.lean` is the geometry- and
  dimension-independent root.  A parameter type and a family of additive
  complex charges determine the universal determinant wall; parameter
  reindexing and additive class pullback preserve it.  The parameter and class
  universes are independent, which is needed for later relative/family
  parameter spaces;
* `StabilityCondition/Walls/Numerical/ChargeFamily.lean` packages the existing
  three-coordinate `(s,t)` charge as one child and proves that the universal
  determinant is exactly the established `wallExpr`.  Circle, line,
  disjointness, and nesting results therefore remain specialized consequences
  of that polynomial child, not assumptions on every central charge;

* `Numerical/Stability/TwistedChern.lean` defines an arbitrary numerical
  codimension-one `BField`, the components of `ch^B = exp(-B)ch`, their
  degree-zero/one/two expansions, and the theorem identifying the notation
  `B = βH` with the existing `chBetaComp` notation;
* `Numerical/Stability/SurfaceCharge.lean` contains the pure additive charge
  coordinates after twisting, the canonical shared charge polynomial, the
  real scalar specialization `B = bH`, and the coordinate-preserving map
  interface;
* `Numerical/Stability/SurfaceChargeNumerical.lean` adapts one explicit
  `NumericalVarietyData`, `Polarization`, and arbitrary `BField` to those
  coordinates, and proves that `B = βH` agrees with the scalar notation; and
* `Numerical/Examples/Surface/ProjectivePlaneCharge.lean` is a concrete
  rank-one child of the divisorial construction. It supplies the divisor
  space `N¹(P²)_R`, full Chern characters on a placeholder integral `(r,c,v)`
  carrier and on the `SurfaceNum` presentation, the coordinate map between
  them (which is the identity on coordinates), the rank-one `p2BField`, and
  the arithmetic identity between the exponential presentation
  `-∫ exp(-(b + i a)H) ch` and the twisted surface presentation `Z_{aH,bH}`.
  The `(r,c,v)` carrier is **not** Li's image lattice `Λ_ι`; see C2;
* `Numerical/Stability/DivisorialCharge.lean` supplies the intrinsic
  higher-Picard-rank layer: a real divisor space with symmetric intersection
  form, uncompressed additive Chern-character coordinates, independent
  `(B,omega)` parameters, an optional ample-cone witness, the arbitrary real
  `B`-twist, the general divisorial charge, its Mukai-pairing expression, and
  the theorem recovering the existing scalar-twist API on
  `B = beta H`, `omega = alpha H`; and
* `Numerical/Stability/DivisorialWallSlice.lean` makes the arbitrary
  `(B,omega)` divisorial charge into a full wall family.  Orthogonal slices are
  literal parameter reindexings of that parent, with an arbitrary real
  transverse parameter space.  The intrinsic `H-perp` constructor and its
  decomposition theorem show that `B=sH+G` loses no real `B` directions when
  `H^2` is nonzero; Hodge signature and ampleness remain separate certificates;
* `Numerical/Stability/DivisorialChargeNumerical.lean` supplies the
  scalar-extension bridge from the codimension-one piece of a rational
  `NumericalRingData` to an arbitrary real `DivisorSpace`. Its
  `NumericalRealization` preserves rational scalar multiplication and the
  intersection form independently of any class carrier or Todd data. For
  every `NumericalVarietyData` using that ring, it constructs the full real
  `ChernCharacter` and proves equality of the intrinsic real charge with
  `ofNumericalDataB` for every rational `BField` and every real polarization
  scale; and
* `Numerical/Examples/Surface/SmoothQuadric.lean` constructs the honest
  rational graded ring `ℚ[f₁,f₂]/(f₁²,f₂²)` with weights `0,1,1,2`,
  degree `∫f₁f₂=1`, Todd class `1+(f₁+f₂)+f₁f₂`, the integral
  `(r,c,d,v)` numerical presentation and its HRR witness. It also proves that
  the codimension-one piece is the span of both rulings and realizes it in
  `N¹(P¹×P¹)_ℝ`, preserving the full intersection form; and
* `Numerical/Examples/Surface/SmoothQuadricCharge.lean` is the corresponding
  rank-two child of the divisorial construction. Its Chern character is
  induced by that realization. It records the actual ample cone, expands the
  charge for arbitrary real `(b₁,b₂)`, compares rational ample and `B`
  parameters to `ofNumericalDataB`, and proves that a nonzero anti-diagonal
  `B`-field is invisible to the scalar ansatz `B = beta(f₁+f₂)`.  Its
  inherited wall family takes `U=R` and `G(u)=u(f₁-f₂)`; and
* `Numerical/Stability/WallTransport.lean` now bundles its degree-weighted
  surface transport as an additive map and pulls back the generic `(s,t)`
  charge family.  The Picard-rank-one K3 model is an explicit child of this
  route.  This is an ordinary-Chern-coordinate wall adapter; a Todd-corrected
  Mukai charge must remain a separately named class-map adapter.  The
  transport compresses the first Chern class to `H · ch₁`, so on a surface of
  Picard rank greater than one it is the `H`-slice only, never the full wall
  family of the surface; and
* `Numerical/Stability/DivisorialWallTransport.lean` joins the two branches
  of the hierarchy below.  For any `NumericalRealization`, the compressed
  `(s,t)` family pulled back through `toNumClassHom` is literally the
  reindexing of the intrinsic divisorial family along the rank-one slice
  `B = sH`, `omega = tH` (`wallChargeFamily_eq_rankOne_reindex`).  Every
  rank-one child therefore reaches both the circle/line/nesting theorems of
  the `(s,t)` polynomial and the arbitrary-`(B,omega)` divisorial layer; and
* `Numerical/Stability/DivisorialDiscriminant.lean` supplies the
  Macrì--Schmidt discriminants `Δ`, `ar Δ^B_ω`, `Δ^C_{ω,B}` on the intrinsic
  character, the divisor-space Hodge index certificate `DivisorSpace.HodgeIndex`
  with its one-directional bridge to the numerical `HodgeIndexStatement`, the
  derivation of `OrthogonalSlice.IsHodge` from the inequality plus
  nondegeneracy, and the transport of `BogomolovGiesekerData` to
  `0 ≤ ar Δ^B_ω` under a Hodge index at `omega`; and
* `Numerical/Stability/DivisorialWallCircle.lean` proves that fixing the
  transverse parameter turns a divisorial slice into the `(s,t)` model itself:
  `chargeFamily_reindex_ofST` identifies the reindexed family with
  `stChargeFamily` pulled back along the degree-weighted triple of the
  `G(u)`-twisted character.  The circle, vertical-line, disjointness and
  nesting results of `Walls/Numerical/` therefore hold on every `u`-plane of a
  surface of arbitrary Picard rank, and `barDiscriminant_parameters` discharges
  their `0 ≤ discr` hypothesis from the supplied Bogomolov and Hodge data.  The
  walls do move with `u`: `discr_sliceCoordinates` records by how much.  The
  wall root additionally carries the real-linear action on charges, with
  `wallValue_linearAct` the determinant law and `wall_linearAct`/`wall_smul` its
  invariance consequence — the numerical half of the `GL⁺(2,ℝ)` action that C5
  needs.

`NumericalRingData` is presently a rational intersection ring, so its
arbitrary `BField` is rational. The divisorial layer handles a fully arbitrary
real `B ∈ N¹(X)_ℝ` without changing the charge polynomial, and
`NumericalRealization` now provides the rational-to-real bridge. The `P²`
model instantiates it by proving that its codimension-one piece is the span of
`H` and realizing `x` as `∫xH`. What remains is a concrete higher-rank
intersection-ring model and realization, plus the eventual geometric map from
actual numerical cycle classes.

The shared parent is the construction in `DivisorialCharge.lean`:
`DivisorSpace`, a full `ChernCharacter`, and independent
`StabilityParameters` determine the intrinsic central charge. Both `P²` and
the smooth quadric instantiate those parent inputs; neither example owns the
general formula. In Lean this is structural composition rather than nominal
object-oriented subclassing. The two `P²` class carriers are distinct Lean
types with identical coordinates, connected by a full-character `Pullback`
before choosing `B` and `omega`, so one comparison theorem transports every
parameter choice. The carrier distinction is a placeholder for a later
geometric `vLi` map; it carries no information about `K₀(P²)` or `Λ_ι` today.

This module is intentionally still not a geometric `K₀(ℙ²)` image, a
stability condition, a heart, or a source-backed projective-family theorem.
Those remain inputs for the future C1--C5 package.

## Higher-Picard-rank literature audit

The abstraction above follows the primary surface literature rather than
extrapolating the `P²` coordinate record:

* [Bridgeland, arXiv:math/0307164](https://arxiv.org/abs/math/0307164)
  packages a K3 numerical class as the Mukai vector
  `v(E)=ch(E)sqrt(td_X)` and writes its charge as the Mukai pairing with
  `exp(B+i omega)`. The divisor slot and its intersection form corroborate the
  same intrinsic layer, but the third coordinate is `s=ch₂+rank`, not raw
  `ch₂`. A future Mukai adapter must therefore be explicit and must not inhabit
  a field whose contract says it contains the ordinary Chern character.
* [Maciocia, arXiv:1202.4587](https://arxiv.org/abs/1202.4587) identifies
  numerical classes with `(r,c₁,ch₂)`, takes `B=beta` in the full
  `NS(X)_R`, and writes the central charge explicitly using the intersection
  form. After fixing an ample `omega`, he decomposes
  `beta=b omega+gamma` with `gamma.omega=0`, then studies the family
  `B=s omega+u gamma`, `omega'=t omega`. This is a choice of wall-computation
  coordinates after the intrinsic charge has been defined.
* [Arcara--Miles, arXiv:1401.6149](https://arxiv.org/abs/1401.6149) likewise
  starts with independent real divisors `(D,H)` and
  `Z=-integral exp(-(D+iH))ch`. For Picard rank greater than one it normalizes
  `H²=1`, chooses `G.H=0`, `G²=-1`, and studies the three-dimensional slices
  `D=sH+uG`, `omega=tH`. Their Picard-rank-two and Hirzebruch-surface analysis
  depends essentially on the orthogonal `u` direction.
* [Altavilla, arXiv:1905.10636](https://arxiv.org/abs/1905.10636) records the
  general `B`-twisted character and charge first, then restricts the
  `P¹ x P¹` computations to the `(alpha,beta)` slice. The two rulings satisfy
  `D₁²=D₂²=0`, `D₁.D₂=1`; the paper alternates between `H=(1,1)` and
  `H=(1,2)` because the compressed invariant `H.ch₁` can otherwise identify
  distinct divisor classes. This is direct evidence against making the
  compressed degree the source of truth.
* [Mizuno--Yoshida, arXiv:2502.18894v2](https://arxiv.org/abs/2502.18894v2)
  (v2, 2025-05-21) treats the blow-up of `P²` at two points. Its Section 2.1
  chooses an orthogonal basis `H,G₁,G₂` with `H² = 1`, `G₁² = G₂² = -1`
  (signature `(1,2)`) and uses
  `D=sH+u₁G₁+u₂G₂`, `omega=tH`, producing a four-real-parameter slice. The
  number of orthogonal `u` coordinates grows with Picard rank, while the
  intrinsic data remain one divisor vector `B` and one ample vector `omega`.

These examples fix the architectural rule: bases, orthogonal decompositions,
and `(alpha,beta)` planes are downstream parameterizations. The core owns the
real vector space and bilinear form. Ampleness is a separate geometric
predicate; positive square alone is not used as its definition. The existing
`Surface.ChargeCoordinates` remains a useful terminal projection after `B`
and `omega` have been chosen, not a representation of the full divisor data.

## Non-goals fixed by this contract

* No assertion that Li's pulled-back heart equals the Macrì--Schmidt HRS
  heart without a slicing theorem.
* No deletion of the Todd correction and no silent replacement of `td_X` by
  `sqrt(td_X)` or a Mukai vector.
* No identification of Li's two parameters with arbitrary `ω,B` in higher
  Picard rank.
* No use of `BMTData` for the surface argument.
* No concrete smooth projective surface/family, derived-category realization,
  relative HN filtration, openness, boundedness, or moduli space manufactured
  with an axiom, `sorry`, or an inhabited placeholder.
* No status promotion in either coverage map. The maps remain source ledgers,
  not trust records.

## Current wall hierarchy and next coding boundary

The implemented ownership tree is:

```text
Wall.ChargeFamily P N                         arbitrary variety/family root
|- Wall.stChargeFamily                       the three-coordinate (s,t) child
|  `- Surface.wallChargeFamily               polarised-surface class pullback
|     `- Examples.k3WallChargeFamily         rank-one K3 numerical child
`- ChernCharacter.fullChargeFamily           arbitrary surface (B,omega)
   `- OrthogonalSlice.chargeFamily            reindexed B=sH+G(u), omega=tH
      |- p2ProjectiveWallFamily               U=0
      `- SmoothQuadric.wallChargeFamily       U=R, G(u)=u(f1-f2)
```

The two branches are joined by `wallChargeFamily_eq_rankOne_reindex` in
`DivisorialWallTransport.lean`: for every `NumericalRealization`, the left
branch is the reindexing of the right branch along `B = sH`, `omega = tH`.
Until that theorem existed the hierarchy was a forest with two independent
formula owners (`reZ`/`imZ` and `ChernCharacter.centralCharge`); the theorem
is what makes it one tree.

This is structural composition and pullback, not nominal object-oriented
inheritance.  It leaves the universal wall determinant usable for future
threefold/BMT charges and for any smooth projective variety, while keeping
circle and nesting calculations where their special polynomial form is
actually available.  A dependent variant `charge : (p : P) → N p →+ ℂ`, for a
local system of lattices with monodromy, is not modelled and is not needed
for the projective-family case, where one lattice serves the whole family
(Theorem 10.3).

The next honest coding boundary is one of:

1. move the generic `SurfaceCharge`/`DivisorialCharge` layer out of
   `AlgebraicGeometry/` (the candidate lane recorded in
   `docs/architecture/cutover-ledger.md`) and redefine `Wall.stChargeFamily` as
   a reindexing of `ChernCharacter.fullChargeFamily`, so that one formula owner
   remains and `DivisorialWallTransport.lean`'s bridge becomes a definition;
2. name the Mukai adapter explicitly: a `ChernCharacter → Mukai.RealExtension`
   map whose third slot is `ch₂ + rank`, tied to `Examples/Surface/K3Mukai.lean`,
   so Bridgeland's charge is a second child rather than an overload of a field
   whose contract says it holds the ordinary Chern character;
3. define a threefold/BMT central-charge family as another child of
   `Wall.ChargeFamily`, with its own character structure carrying `ch₃` and a
   cubic twist, without promoting the conjectural BMT inequality to a generic
   fact;
4. add topological chamber and connected-component structure above generic wall
   sets, only when a topology and local-finiteness hypotheses are explicitly
   available;
5. connect `Wall.ChargeFamily` to the existing categorical family interfaces
   once #851 supplies the common relative numerical class-map data, using
   reindexing for base change rather than inventing a second family carrier; or
6. implement the C1 numerical comparison after the geometric `vLi`/GRR data
   have an honest owner.

The current layer fixes the formulas, source locations, normalization choices,
and supplied hypotheses without claiming that the two stability conditions
are equal.
