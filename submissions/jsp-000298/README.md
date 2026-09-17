# Lean 4 Formalization for Erdős Problem JSP-000298

This package provides a standalone, reproducible Lean 4 formalization of structural subset-sum avoidance bounds for Erdős Problem JSP-000298, based on:
> Noga Alon and Paul Erdős, *Sure monochromatic subset sums*, Acta Arithmetica 74(3), 1996, pp. 269–272.

## Reproduction Instructions

Using `elan` (Lean version manager):

```bash
# Enter this submission directory
cd submissions/jsp-000298

# Fetch mathlib cache
lake exe cache get

# Build the Erdos298 library
lake build
```

## Formalized Theorems
- `Erdos298.no_one_coloring_of_ge_three`: Non-trivial chromatic lower bound $f(n) \ge 2$ for all $n \ge 3$.
- `Erdos298.upper_half_subset_sum_free`: The upper interval block $[\lceil n/2 \rceil, n-1]$ is subset-sum-free for $n$ (Alon–Erdős 1996, Section 2, $k=1$).
- `Erdos298.dvd_subset_sum_free`: Multiples of any non-divisor $m \nmid n$ form a subset-sum-free class (Alon–Erdős 1996, Section 2).
- `Erdos298.erdos_298_structural_bounds`: Main structural theorem combining lower and interval bounds with 0 sorry and standard axioms.