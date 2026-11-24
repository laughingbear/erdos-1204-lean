# Erdős Problem 1204 — upper bounds, formalized in Lean 4

Proofs of `Erdos1204.erdos_1204.variants.A_upper` and `Erdos1204.erdos_1204.variants.B_upper`
from [google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures)
(`FormalConjectures/ErdosProblems/1204.lean`):

* $A(k) \le (1+o(1))\,k\log k$ and
* $B(k) \le (1/2+o(1))\,k\log k$,

where $A(k)$ is the least possible largest element, and $B(k)$ the least possible average, of an
admissible set of $k$ natural numbers (one that misses a residue class modulo every prime).

Construction: the $k$ smallest primes larger than $k$. The asymptotics come from
$p_n \sim n\log n$ (`nth_prime_asymp`) and $\pi(x) \sim x/\log x$ (`pi_alt'`) in
[PrimeNumberTheoremAnd](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd),
pinned at `a4fb698` (Lean v4.35.0).

* `#print axioms` for both theorems gives `[propext, Classical.choice, Quot.sound]`.
* `IsAdmissible`, `A`, `minSum`, `B` and `A_le` are copied verbatim from formal-conjectures, and
  both theorem statements are textually identical.

Build: `lake exe cache get && lake build`.

Prepared with AI assistance (Claude); the statement match and axioms were checked by compiling.
