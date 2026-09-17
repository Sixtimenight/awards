# Citation

Candidate under formal verification; review pending.

## English

Noga Alon and Paul Erdős resolved Erdős's question on the chromatic number of subset-sum avoidance, proving that the minimum number of colors required to color {1, ..., n-1} such that no monochromatic subset sums to n satisfies sub-linear bounds (Acta Arithmetica 74 (1996), 269–272). This Lean 4 candidate submission formalizes the exact problem formulation and its fundamental structural properties: establishing the non-trivial chromatic lower bound that at least 2 colors are needed for every n >= 3 (ruling out all 1-colorings), formalizing the core Alon–Erdős interval avoidance lemma showing that the upper half [(n+1)/2, n-1] forms a subset-sum-free block, and formalizing the modular avoidance lemma for arithmetic progressions.
