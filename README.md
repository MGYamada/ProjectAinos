# P⊗AI (Project Ainos)

*Final answer to Hilbert's sixth problem*

P⊗AI is pronounced `poai`.

**P⊗AI (Project Ainos)** is a *proof of artificial intelligence* project that seeks to demonstrate AI's capacity for rigorous scientific reasoning through machine-checked proofs.
Taking Hilbert's sixth problem as its starting point, it aims to formalize the whole of theoretical physics in Lean 4.
The proof library makes each theory's assumptions explicit and connects its results to other theories through special cases and limits.

## Table of Contents

### 1. Thermodynamics (Lieb–Yngvason 2.0)

The Lean library derives entropy from adiabatic accessibility, tracks conserved quantities
through mixing and chemical reactions, and constructs an operational ideal-gas model.
[Mathematical guide](docs/thermodynamics.md) · [Models and counterexamples](docs/thermodynamics-models.md)

### 2–5. Mechanics and classical field theory (Landau–Lifshitz 2.0)

The program is complete for Volumes 1 and 2. Lean proofs cover all 52 section targets in
*Mechanics* and all 119 in *The Classical Theory of Fields*. Each ledger records the
hypotheses and scope of the result for each textbook section.

| Topic and proof guide | Textbook sections and ledger | Selected results |
| --- | --- | --- |
| 2. [Mechanics](docs/mechanics.md) | [Vol. 1, §§1–52](docs/cinfty-mechanics.md#ledger) | Least action and conservation laws, scattering, oscillations, rigid bodies, Hamiltonian mechanics and action–angle variables |
| 3. [Special relativity](docs/special-relativity.md) | [Vol. 2, §§1–14](docs/cinfty-special-relativity.md#ledger) | Lorentz transformations, proper time, relativistic collisions and invariant mass-shell measures |
| 4. [Electrodynamics](docs/electrodynamics.md) | [Vol. 2, §§15–80](docs/cinfty-electrodynamics.md#ledger) | Lorentz force, Maxwell equations, diffraction, retarded fields, radiation reaction and scattering |
| 5. [General relativity](docs/general-relativity.md) | [Vol. 2, §§81–119](docs/cinfty-general-relativity.md#ledger) | Einstein equations, Schwarzschild and Kerr fields, gravitational radiation, spherical collapse and cosmological perturbations |

### 6. Classical statistical mechanics (Goldstein–Lebowitz 2.0)

The next research program starts with Hamiltonian phase volume and the Boltzmann entropy
of a macrostate. It asks when typical systems spend most of their time in equilibrium
and how the ideal-gas entropy and adiabatic comparison of Topic 1 emerge in the
thermodynamic limit. [Six-part outline and references](docs/research-overview.md#classical-statistical-mechanics)

## Further reading

- [Research overview and references](docs/research-overview.md) gives the field-theory results by subject and links to the individual proofs.
- [Shared smooth algebra and geometry](docs/shared-smooth-algebra-and-geometry.md) and the [Courant–Hilbert correspondence](docs/courant-hilbert.md) describe the mathematical foundations.
- The quantum prototypes cover a [qubit](docs/quantum-mechanics-prototype.md) and a [scalar smeared field](docs/quantum-field-theory-prototype.md).
- The [documentation index](docs/README.md) links to the proof maps, implementation history, and handbook build instructions.

## Textbook references

The “2.0” labels name Project Ainos's research programs. Topic 1 draws on
E. H. Lieb and J. Yngvason, *The Physics and Mathematics of the Second Law of
Thermodynamics*, *Physics Reports* 310(1) (1999), pp. 1–96.
[Published article](https://doi.org/10.1016/S0370-1573(98)00082-9) ·
[Open preprint](https://arxiv.org/abs/cond-mat/9708200)

Topic 2 follows L. D. Landau and E. M. Lifshitz's *Mechanics*, Volume 1 of the
*Course of Theoretical Physics*, 3rd English edition (1976).
[Publisher's catalogue](https://shop.elsevier.com/books/mechanics/landau/978-0-08-050347-9)

Topics 3, 4, and 5 follow Chapters I–II, III–IX, and X–XIV, respectively, of
Landau and Lifshitz's *The Classical Theory of Fields*, Volume 2 of the
*Course of Theoretical Physics*, 4th revised English edition.
[Publisher's catalogue](https://shop.elsevier.com/books/the-classical-theory-of-fields/landau/978-0-08-025072-4) ·
[Chapter correspondence](docs/landau-lifshitz.md#special-relativity)

## License

[Apache License 2.0](LICENSE) · [Copyright notice](NOTICE)
