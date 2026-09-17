# Citation

Candidate under formal verification; review pending.

## English

Erdős Problem JSP-000298 (Erdős Problem #360) investigates the minimum number of colors $f(n)$ required to color the integers $\{1, \dots, n-1\}$ such that no monochromatic subset sums to $n$. Originally posed by Erdős and Graham (1980), bounds of order $n^{1/3 \pm o(1)}$ were established by Noga Alon and Paul Erdős (*Acta Arithmetica* 74(3), 1996, pp. 269–272), with further sharp order bounds established by Conlon, Fox, and Pham (2021). This machine-checked Lean 4 candidate submission formalizes an elementary, constructive cubic-root upper bound: for all $n \ge 2, s \ge 1$ with $n \le s^3$, there exists an explicit coloring with $2s$ colors avoiding monochromatic subset sum $n$ (`exists_coloring_of_le_cube`), establishing $f(n) \le 2\lceil n^{1/3}\rceil$. The submission also formalizes the general interval avoidance theorem for any $k \ge 1$ (`interval_block_avoids_subset_sum`), modular divisibility avoidance (`dvd_subset_sum_free`), and the non-trivial lower bound $f(n) \ge 2$ for all $n \ge 3$ (`minColors_ge_two`).