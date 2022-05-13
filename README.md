#  General Topology - Logika v računalništvu student project

## Project Roadmap

### Preliminaries

You may not need all of these, but be ready to formalize them as needed:

- [ ] assume excluded middle
- [X] define subset of `X` as a map `X → Prop` (powerset of `X` is `X → Prop`, this requires `{-# OPTIONS --prop #-}`)
- [ ] show that the powerset is a complete lattice (given any family of subsets, define their union and intersection)
- [ ] given `f : X → Y`, define the inverse image map `f^* : P(Y) → P(X)`
- [ ] direct image map `f_* : P(X) → P(Y)` 
- [ ] subset of a set
- [ ] family of subsets
- [ ] union of a family of subsets
- [ ] inverse image preserves unions and finite intersections
- [ ] countable set

### Topologies - N

- [X] topology on a set
- [ ] topology generated by a base (a family of subsets closed under finite intersections)
- [ ] the base generated by a subbase (close the subbase under finite intersections)
- [X] examples
  - [X] trivial topology
  - [X] discrete topology
- [ ] partial ordering on the topologies on a set `X`
- [ ] the trivial topology is the smallest and the discrete topology the largest one
- [ ] topologies on a given set form a complete lattice
- [ ] the topology generated by a subbasis is the least topology that contains the subbasis

### Continuous maps - G

- [X] definition of a continuous map (inverse image preserves opens)
- [X] continuous map is continuous
- [X] constant map is continuous
- [X] composition of continuous maps is continuous
- [X] every map from space with discrete topology is continuous
- [X] every map to space with indiscrete topology is continuous
- [X] definition of a homeomorphism
- [X] identity map is a homeomorphism
- [X] compositions of homeomorphism is homeomorphism
- [X] inverse of homeomorphism is homeomorphism

### Constructions - N*

- [ ] definition of a subset of a space
- [ ] the subspace topology, and its universal property (smallest topology for which inclusion is continuous)
- [ ] the product of two spaces, and its univeral property
- [ ] the product of a family of spaces, and its universal property
- [ ] the coproduct of two spaces, and its universal property
- [ ] the coproduct of a family of spaces, and its universal property

### Covers - G*

- [ ] definition of an open cover of a subset
- [ ] definition of a subcover
- [ ] definition of a finite subcover
- [ ] definition of a refinement of a cover
- [ ] if the topology of `X` is generated by a basis `B`, then every open cover has a refinement consisting of basic open sets

### Properties of spaces - K*

- [ ] Hausdorff space
- [ ] 2-countable space (the topology is generated by a countable set of opens)
- [ ] 0-dimensional space (has a basis of open-closed/clopen subsets)

### Compactness

- [ ] compact subset (every open cover has a finite subcover)
- [ ] finite subset if compact
- [ ] a continuous image of a compact subset is compact
- [ ] the compact subsets of a discrete space are the finite subsets
- [ ] closed subset of a compact space is compact
- [ ] compact subset of a Hausdorff space is closed

### Cantor space 𝕂

- [ ] Cantor space 𝕂 (the set ℕ → 2 with product topology)
- [ ] 𝕂 is Hausdorff
- [ ] 𝕂 is compact
- [ ] 𝕂 is 2-countable
- [ ] 𝕂 is 0-dimensional
- [ ] 𝕂 × 𝕂 is homeomorphic to 𝕂
- [ ] 𝕂 is homogeneous (for any `α, β ∈ 𝕂` there is a homeomorphism `h : 𝕂 → 𝕂` such that `h α = β`

### Sierpinski space 𝕊

- [ ] Sierpinski space (`{⊥, ⊤}` with topology `{∅, {⊤}, {⊥, ⊤}}`)
- [ ] Sierpinski space is `T₀` (if two points have the same neighborhoods then they are equal)
- [ ] Sierpinski space is compact
- [ ] Sierpinski space is not Hausdorff
- [ ] Sierpinski space characterizes open sets (continuous maps `X → 𝕊` are in bijective correspondence with open subsets of `X`)
