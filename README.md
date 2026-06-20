# vertexAlg

This is a repository for experimenting with vertex algebra API in lean4 + mathlib4.

## Main Goals

 * Construct the Monster Vertex Operator Algebra `V♮` (also known as the `Moonshine Module`)
 * ([Show that the automorphism group of `V♮` is finite and simple](https://arxiv.org/abs/2206.15391))
 * Prove `Theorem (Borcherds 1992)`: The Conway-Norton Monstrous Moonshine Conjecture holds for `V♮`.

## Possible additional goals (if I don't get too old doing the main goals first)

 * Tensor structure for modules (Huang-Lepowsky-Zhang)
 * Verlinde formula (Huang)
 * ([Regularity for fixed point subalgebras](https://arxiv.org/abs/1603.05645))
 * ([Generalized moonshine](https://arxiv.org/abs/1208.6254))
 * ([The standard self-dual integral form of `V♮`](https://arxiv.org/abs/1710.00737))
 * ([Modular and integral moonshine](https://arxiv.org/abs/2111.09404))
 * Chiral de Rham, topological line defects, classification of K3 CFTs and orbifolds, 4D-2D duality

## Done so far

 * Definition of vertex algebra
 * some formal power series manipulations
 * loop algebras
 * Lie algebra extensions and 2-cocycles

## TODO

 * Group theory: Golay-24 code, Mathieu₂₄, A₁²⁴ Niemeier lattice, Leech lattice, Conway₁, show that the action of Conway₀ on Leech/2Leech is irreducible.
 * Vertex algebras: Dong's lemma, Jacobi identity for local fields, Vacuum representations, invariant inner products, Lattice vertex algebras, -1-twisted module for lattices, -1 lattice orbifold, weight one Lie algebra action, worldsheet symmetry classes
 * Lie algebras: Positive energy representations, vertex operators attached to Lie algebra elements, generalized Kac-Moody Lie algebras, twisted denominator formula, virasoro representations, no-ghost theorem
 * Modular functions: Hauptmoduls, Hecke-monic functions and replicability
 * Power series: clean up binomial series, better API for passing between Hahn series and coefficients
 * K-theory: Lambda-rings, Adams operations
 * Algebraic groups: Trivial Lie algebra implies finite
