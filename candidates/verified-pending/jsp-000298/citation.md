# Citation

Candidate under formal verification; review pending.

## English

Noga Alon and Paul Erdős resolved Erdős's question on the chromatic number of subset-sum avoidance, proving that the minimum number of colors $f(n)$ required to color $\{1, \dots, n-1\}$ such that no monochromatic subset sums to $n$ satisfies sub-linear bounds (Acta Arithmetica 74(3), 1996, pp. 269–272). This Lean 4 candidate submission formalizes the problem definitions and core structural avoidance properties from Section 2 of the paper: establishing the non-trivial chromatic lower bound that at least 2 colors are needed for every $n \ge 3$ (ruling out all 1-colorings), formalizing the upper-half interval avoidance lemma showing that $[\lceil n/2 \rceil, n-1]$ forms a subset-sum-free block (the $k=1$ case of the Alon–Erdős interval partition method), and formalizing the modular divisibility avoidance lemma for arithmetic progressions.