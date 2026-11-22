# Research overview and references

## The classical theory of fields

The C∞ research trilogy gives section-level targets for Volume 2 of Landau and Lifshitz.
The plans record the mathematical assumptions and link each result to its Lean proof.
[Special Relativity, §§1–14](cinfty-special-relativity.md),
[Electrodynamics, §§15–80](cinfty-electrodynamics.md), and
[General Relativity, §§81–119](cinfty-general-relativity.md).
All 119 section targets are proved within the scopes recorded in the three ledgers.
The original plan included the free relativistic particle, the Maxwell action with a
prescribed current, and the differential Bianchi identity. The two subsequent issues
tracked the proofs and the sections that still had a stated remainder.
[Original plan](https://github.com/MGYamada/ProjectAinos/issues/8) ·
[Section proofs](https://github.com/MGYamada/ProjectAinos/issues/135) ·
[Remaining targets](https://github.com/MGYamada/ProjectAinos/issues/187)

### Special relativity

For the free relativistic particle the library proves the coordinate-time
Hamiltonian `√(m² + Σ pᵢ²)` with its trajectories and its flow, the Poincaré
algebra of the orbital charges with its contraction to the Galilei algebra,
and the reduction of the future sheet of the mass shell to the phase space of
the initial data.
[Guide](special-relativity.md#relativistic-particle-mechanics-the-algebraic-layer)
It also proves that the inertial clock measures the greatest proper time, that
the stationary curves of the free action are the inertial motions, the energy
and the momentum measured by an observer, the Legendre transformation on the
ball of velocities, and the expansion in `1/c` with uniform remainders.
[Guide](special-relativity.md#the-motion-of-a-free-particle)
For the Lorentz group and for collisions it proves that every orthochronous
transformation is a rotation after a boost in one way only, the invariance of
a relation of signals that is contained in the causal order, the energies and
the momenta of a decay into two particles, and the invariants of an elastic
collision.
[Guide](special-relativity.md#signals-the-factorization-of-a-lorentz-transformation-and-collisions)
The future mass shell is a graph over the space momenta on which the Lorentz
group acts smoothly, and the action with an auxiliary field describes the
massive and the massless particle together.
[Guide](special-relativity.md#the-mass-shell-and-the-massless-particle)
The measure `dᵈπ/E` of the shell is invariant under the Lorentz group, the
number of particles through a hypersurface is invariant, and for a system of
particles the orbital moment is conserved and the centre of energy moves
uniformly. The final states of two or more outgoing particles at a fixed total momentum carry a
covariant measure into which the product of the shell measures disintegrates, so the
cross-section is a Lorentz scalar for a scalar transition weight.
[Guide](special-relativity.md#measures-and-charges)
The universal C∞ cotangent module, with the full chain rule and its universal property, matches
the covectors of space-time, which completes the special-relativity ledger.
[Guide](special-relativity.md#four-vectors-and-the-universal-cotangent-module-6)

### Electrodynamics

For electrodynamics, a charge in static potentials has the Hamiltonian
`√(m² + Σ (pᵢ − e aᵢ)²) + e φ`; its equations are the equation of the Lorentz
force, its flow exists for all times, and they are the stationary curves of
the action of space-time. In a constant field the motion in the proper time
is solved for every field, with a closed form of the four-velocity in each
of the four cases of the invariants `B² − E²` and `E · B`. The components of
`E` and `B` for a moving observer are derived from the boost, and on a
manifold the field of a potential is closed, gauge invariant and natural.
[Guide](electrodynamics.md#a-charge-in-a-given-field-1525)
On a curved background the action of a charge is stationary exactly when
`m ∇_τ U = −e (ι_U F)^♯`, and the action of the field with a prescribed current
exactly when `dH = J`; at the Minkowski metric both are the flat actions.
[Guide](electrodynamics.md#the-field-and-a-charge-on-a-curved-background-17-27-90)

The local Lagrangians of fields form a jet ring with commuting total
derivatives. In it a divergence is a null Lagrangian, and Noether's identity
and the conservation of the canonical stress tensor hold for a Lagrangian of
the first order. [Guide](variational.md#jet-rings-of-fields)

With a prescribed current the field action gives `dH = J`, it is gauge
invariant exactly when the current is closed, and the source term has the
sign of the coupling of a charge. The four equations of Maxwell for `E` and
`B` follow, and the charge in a box changes by the flux through its faces.
[Guide](electrodynamics.md#the-field-with-a-current-2630)
The theorem of Poynting and the balance of the momentum hold in an inertial
frame and on a box, the stress tensor of the field is symmetric and
trace-free with the energy density `½ (E² + B²)` for every observer, and with
charged dust the total stress is conserved.
[Guide](electrodynamics.md#energy-and-momentum-31-3335)
For a stress tensor supported in a box the time average of the spatial stress vanishes, a
relativistic charge in a Coulomb field moves on a rosette or falls to the centre in finite time,
and in a uniform magnetic field charges with a common `e/m` move as in a frame rotating at the
Larmor frequency, up to an explicitly bounded term.
[Guide](electrodynamics.md#the-virial-theorem-the-coulomb-field-and-larmors-theorem-34-39-45)
A smooth charge has a unique decaying potential with `−Δφ = ρ` and a finite energy, a moving charge
has the boosted field, in Lorenz gauge the field equations are wave equations, plane waves have
two polarizations, and the coherency matrix of partially polarized light is positive.
[Guide](electrodynamics.md#static-fields-the-moving-charge-and-waves-3638-4648-50)
Localized charges and currents have multipole expansions with uniform remainders. In order ℓ,
the electric potential has exactly 2ℓ + 1 real spherical components. The corresponding series
for the mutual energy converges when the enclosing charge balls are disjoint. A conserved
current has a unique static magnetic field with a magnetic moment of `e/2m` times the angular
momentum, the wave equation and the Coulomb field are resolved in Fourier components, and the field
in a periodic box is a sum of modes. A perfectly conducting circular cylinder admits axial
Maxwell modes at arbitrarily high zeros of J₀(kR). In a conducting ball the dipole modes
satisfy both wall conditions at the positive zeros of j₁(kR).
[Guide](electrodynamics.md#multipoles-magnetostatics-and-the-fourier-resolution-4044-49-51-52)
The retarded potentials of a conserved current are given by an explicit integral that solves
Maxwell's equations with causal support, and their time transform solves the Helmholtz equation.
[Guide](electrodynamics.md#the-retarded-potentials-62-64)
A point charge on a world line slower than light has the Liénard–Wiechert field and is its source,
slow charges interact through the Darwin Lagrangian to second order, a localized source radiates
the power of its far-field amplitude with dipole, quadrupole and magnetic-dipole terms, and a fast
charge radiates with Liénard's power, concentrated in a narrow cone. For circular motion the
observed polarizations give the power in each harmonic. Near the critical frequency γ³|Ω| the
angular spectrum has the two Macdonald profiles K⅓ and K⅔.
[Guide](electrodynamics.md#radiation-63-6567-7174-77)
High-frequency fields satisfy the eikonal and transport equations at their leading orders, with
null rays, conserved intensity and Fermat's principle; wave fronts focus by a Riccati law, ideal
instruments are similarities, and the error of geometrical optics is bounded by the wave energy.
For a single real wave with a nonstationary spatial phase on the amplitude supports, ε² times its
energy tends to half the leading intensity of the quadrature pair.
[Guide](electrodynamics.md#geometrical-optics-5358)
The straight-edge Fresnel intensity equals one quarter on the shadow boundary.
Light diffracted by an aperture is the unique radiating solution with the aperture data on the plane,
with one polarization of the Maxwell field, and has the Fresnel and Fraunhofer forms with explicit
remainders, a
radiating charge feels a damping force — for a rigid charge of finite size the self-consistent motion
follows the reduced equation of radiation damping, and the covariant force follows from the flux of
the field through a thin tube around the world line — and free and bound charges scatter waves with the Thomson
and Rayleigh cross sections.
[Guide](electrodynamics.md#diffraction-5961) ·
[Guide](electrodynamics.md#radiation-damping-and-scattering-75-76-7880)
Colliding charges radiate with the dipole spectrum, whose low-frequency end is fixed by the
change of velocity. On a Kepler ellipse the two Cartesian acceleration harmonics are given by
Jₙ(nε) and J′ₙ(nε). For either sign of the Coulomb interaction, the hyperbolic collision
spectrum is given by the outgoing Hankel function at imaginary order and argument.
[Guide](electrodynamics.md#radiation-in-collisions-6870)

### General relativity

For general relativity, an observer with a timelike velocity measures
distances with a spatial form whose square root is half the proper time of a
light signal to a neighbouring event and back, and in co-ordinates the observer at rest has the
clock `√(−g₀₀)` and the spatial metric `gᵢⱼ − g₀ᵢ g₀ⱼ/g₀₀`. Along a geodesic the
pairing of a Killing field with the velocity is constant, and the frequency
measured by stationary observers obeys the red shift `N ω = const`; in the
exterior Schwarzschild field this is `√(1 − 2M/r) ω = const` along every
geodesic segment off the axis, radial rays included. In a chart on all of `ℝⁿ`
with coefficients smooth there, the geodesics defined for all values of the
parameter are the trajectories of the Hamiltonian `½ g^{μν} p_μ p_ν`, with the
Killing momenta as integrals. Rotating
co-ordinates in Minkowski space give the slower clocks, the longer
circumference and the synchronization gap of a rotating disc.
[Guide](general-relativity.md#observers-killing-fields-and-rotation-82-84-88-89)
The curvature of every smooth Lorentz metric satisfies the second Bianchi
identity, its contraction `∇^a Ric_{ab} = ½ ∂_b R` holds, and the Einstein
tensor `Ric − (R/2) g` is divergence-free; a conformally flat metric on `ℝ⁴`
with a nonzero Einstein tensor is the test case. Every tensor shape — covectors,
contravariant, mixed and general tensors — has a covariant derivative, the connection that
the Leibniz correction induces on hom bundles, with its chart formulas and `∇g = 0`.
[Guide](general-relativity.md#the-derivative-of-the-curvature-the-bianchi-identities-and-the-einstein-tensor-85-92)
The relative Einstein–Hilbert action of a metric given by coefficients on an
open set of `ℝ⁴` has, for a variation `g + εh` with compact support, the first
variation `(1/2κ) ∫ (G_{ik} + Λ g_{ik}) δg^{ik} √|g| d⁴x`; the divergence term
integrates to zero, and the curved metric `e^{2z} η` gives a nonzero test.
[Guide](general-relativity.md#the-first-variation-of-the-einsteinhilbert-action-93)
With a scalar field or a fixed electromagnetic field, whose Hilbert tensors are
derived from their actions, the total action is stationary under every compactly
supported variation of the metric exactly when the Einstein equations hold, and
their source is then conserved. On a fixed background the scalar field obeys the
Klein–Gordon equation exactly when its action is stationary, and then its stress is
conserved without the Einstein equations.
[Guide](general-relativity.md#matter-and-the-einstein-equations-94-95)
On a fixed background given by coefficients on an open set, the Maxwell equations
`∇_a F^{ab} = j^b` follow from the action of the field, and the covariant Lorentz force
from the action of a charge, with the flat theorems as the Minkowski case.
[Guide](general-relativity.md#the-field-and-a-charge-on-a-fixed-background-90)
In a smooth orthonormal frame the curvature is given by the rotation coefficients and
their frame derivatives, and the Einstein equations are equivalent to their tetrad form.
[Guide](general-relativity.md#orthonormal-frames-and-the-tetrad-equations-98)
Geodesics normal to a slice give synchronous co-ordinates, in which the Einstein equations
split into the constraints and the evolution of the spatial metric; de Sitter space in the
flat slicing has `Ric = 3 g`.
[Guide](general-relativity.md#the-synchronous-reference-system-97)
The superpotential of Landau and Lifshitz gives a pseudotensor that vanishes where the first
derivatives of the metric vanish and is the expression (96.9) in the Christoffel symbols, and
with the Einstein equations the total energy and momentum density is conserved in the ordinary
sense.
[Guide](general-relativity.md#the-energy-momentum-pseudotensor-96)
The Schwarzschild field solves the vacuum equations, and within the centrally symmetric ansatz it
is the only vacuum field up to a change of time (Birkhoff); along its geodesics the perihelion
advances by `6πM/(a(1 − e²))` and light is deflected by `4M/ρ`, with remainder bounds.
[Guide](general-relativity.md#the-centrally-symmetric-field-100-101)
The Kerr field solves the vacuum equations, with its ergoregion and frame dragging; with a
comoving fluid the Einstein equations of an isotropic universe are the Friedmann equations,
whose closed, open and flat models are exact solutions, and light is red-shifted by
`a_obs/a_em`.
[Guide](general-relativity.md#the-rotating-field-104) ·
[Guide](general-relativity.md#isotropic-cosmology-111114)
For a given invariant frame the Einstein equations of a homogeneous universe reduce to ordinary
differential equations, the structure constants satisfy the Jacobi identity exactly when
`n a = 0`, and the Kasner metric is a vacuum solution exactly when `Σp = Σp² = 1` or `p = 0`,
with an exact dust-filled solution.
[Guide](general-relativity.md#homogeneous-cosmological-models-116-117)
Static weak fields satisfy the Poisson equation to order `ε`, the linearized field equations are
the derivative of an actual family of metrics with two polarizations for every null wave vector,
and exact plane waves solve `L'' + β'²L = 0`, with a curved strong wave and a second-order residual
of a first-order solution.
[Guide](general-relativity.md#the-newtonian-limit-and-gravitational-waves-99-107-109)
The energy and momentum of an isolated system are surface integrals at infinity and form a four-vector
under Lorentz changes of co-ordinates, a stationary source has the far field of its mass and angular
momentum, a localized source
radiates gravitational waves by the quadrupole formula, short waves travel along null geodesics of a
curved background with their amplitude transported and carry the averaged effective stress of
Isaacson, and the time lines of a synchronous system focus under the energy condition. Kasner
universes end at a curvature singularity in a finite proper time, and under the energy condition a
slice that contracts everywhere bounds the length of every maximizing normal geodesic.
[Guide](general-relativity.md#charges-at-infinity-gravitational-radiation-and-focusing-105-108-110-119)
A star collapses through its horizon in a finite proper time, solves the Einstein equations across its
surface in the weak sense, and its event horizon is the boundary of the region from which light still
escapes; test bodies follow the
post-Newtonian equations of motion, `N` bodies follow the Einstein–Infeld–Hoffmann Lagrangian, the
post-Newtonian field of smooth dust solves the Einstein equations to `O(c⁻⁴)`, density
perturbations of a flat universe grow like `t^{2/3}` and every flat perturbation is the sum of its
scalar, vector and tensor parts,
and the approach to a cosmological singularity passes between Kasner epochs. On closed and open
dust backgrounds, discrete S³ harmonics and continuous H³ harmonics give scalar density and
velocity perturbations with two independent time solutions.
[Guide](general-relativity.md#collapse-post-newtonian-motion-perturbations-and-the-oscillating-regime-102-103-106-115-118)

## Classical statistical mechanics

Topic 6 follows the provisional Boltzmannian typicality plan. [Research plan (issue #55)](https://github.com/MGYamada/ProjectAinos/issues/55)

1. **Hamiltonian phase volume and microcanonical conditioning.** Construct invariant
   measures on finite energy windows, then extend conditioning to conserved quantities,
   composition sectors and regular exact-energy shells.
2. **Macrostates, coarse-graining and Boltzmann entropy.** Define macroregions by
   measurable observables and entropy by their normalized volumes. Establish additivity
   for independent systems and compare Boltzmann and Gibbs entropy in and out of equilibrium.
3. **Equilibrium typicality and concentration.** Estimate the volume of the equilibrium
   macroregion for particles in a divided box. Examine the effects of additional conserved
   quantities, disconnected invariant components and phase coexistence.
4. **Dynamics and conditional H-theorems.** Bound equilibrium residence times for
   microcanonical initial states. Study relaxation from low-entropy macroregions under
   approximate macroscopic autonomy, alongside fine-grained Gibbs entropy invariance,
   time reversal, recurrence and nonergodic examples.
5. **Ensembles, thermal contact and thermodynamic limits.** Compare microcanonical
   and canonical ensembles through subsystem marginals and weak coupling. Establish
   finite-size bounds and the hypotheses for ensemble equivalence in interacting systems
   and at phase transitions.
6. **The bridge to axiomatic thermodynamics.** Derive ideal-gas entropy from phase
   volume with the particle-number and normalization conventions explicit. Connect
   extensivity, additivity and stability to macroscopic adiabatic comparison on matched
   equilibrium composition sectors. Identify the positive entropy scale and the linear
   calibration in the conserved quantities.

### Guiding references

- S. Goldstein and J. L. Lebowitz, *On the (Boltzmann) entropy of non-equilibrium systems*,
  *Physica D* 193(1–4) (2004), pp. 53–66.
  [Published article](https://doi.org/10.1016/j.physd.2004.01.008) ·
  [Open preprint (2003)](https://arxiv.org/abs/cond-mat/0304251)
- S. Goldstein, J. L. Lebowitz, R. Tumulka, and N. Zanghì, *Gibbs and Boltzmann
  Entropy in Classical and Quantum Mechanics*, in V. Allori (ed.), *Statistical
  Mechanics and Scientific Explanation: Determinism, Indeterminism and Laws of
  Nature*, World Scientific (2020), pp. 519–581.
  [Published chapter](https://doi.org/10.1142/9789811211720_0014) ·
  [Open preprint (2019)](https://arxiv.org/abs/1903.11870)

For complementary background on equilibrium typicality, see
[H. Tasaki's revised §4.1 of *Statistical Mechanics I*](https://haltasaki.github.io/books/SM/section41.html).
For phase volume, ensembles, and the ideal gas, see
[Landau and Lifshitz, *Statistical Physics*, Vol. 5, Part 1, Chs. I and III–IV](https://shop.elsevier.com/books/course-of-theoretical-physics/landau/978-0-08-023039-9).

The order of topics after 6 is yet to be determined.

## Shared smooth algebra and geometry

The smooth algebra, smooth geometry, and variational libraries provide
the mathematical foundations for mechanics, special relativity,
electrodynamics, and general relativity. The foundation’s implementation
plan and the Lean results for these subjects are documented in
[Shared smooth algebra and geometry](shared-smooth-algebra-and-geometry.md).

The [Courant–Hilbert 2.0 correspondence](courant-hilbert.md) maps the fourteen
chapters of the German first editions to Lean proofs and open problems. The shared
special-functions library starts with Jacobi elliptic functions and the Legendre
polynomials used in orthogonal expansions and the exterior Newton kernel. Fischer
decomposition gives harmonic polynomials in every positive dimension, with
2ℓ + 1 independent restrictions of degree ℓ on the two-sphere. In every positive
ambient dimension these degree spaces form the orthogonal Hilbert sum of real L²
for surface measure.

See the [proof development record](proof-development.md) for the history of the Lean formalization.

## Quantum prototypes

The [scalar smeared-field prototype](quantum-field-theory-prototype.md)
formalizes a common dense domain, operator closability, and positivity of
finite vacuum words for the prospective QFT program in
[#46](https://github.com/MGYamada/ProjectAinos/issues/46). Its locality
predicate has causality-sensitive regressions: bump tests with explicit
spacelike and timelike supports, and a two-point field with noncommuting
insertions that is local exactly when its two points are not spacelike to
each other. These are regression models, not Wightman fields.
The [qubit comparison prototype](quantum-mechanics-prototype.md) is a
provisional finite-dimensional study for
[#45](https://github.com/MGYamada/ProjectAinos/issues/45).

The documentation index links to the guides and the build instructions for the HTML handbook and Lean API reference. [Documentation index](README.md)

## License

Copyright 2026 Masahiko G. Yamada.

Licensed under the [Apache License, Version 2.0](../LICENSE). See [NOTICE](../NOTICE)
for the copyright notice.
