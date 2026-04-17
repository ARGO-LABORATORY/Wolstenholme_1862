# Wolstenholme's Theorem in Lean 4

A complete formal verification of **Wolstenholme's theorem** (1862) in Lean 4 with Mathlib --- the first such formalization in Lean 4.

> **Theorem (Wolstenholme, 1862).** For every prime $p \geq 5$,
> $$\binom{2p}{p} \equiv 2 \pmod{p^3}.$$

The proof contains **zero `sorry`** declarations and **zero `axiom`** declarations. Every lemma is fully machine-checked.

## Repository contents

| File | Description |
|------|-------------|
| `Wolstenholme_1862.lean` | Complete Lean 4 formalization (~800 lines) |
| `wolstenholme_paper.tex` | Accompanying paper (LaTeX source) |
| `wolstenholme_paper.pdf` | Compiled paper |

## Proof architecture

The proof reduces the binomial coefficient congruence to a product identity and proceeds through five stages:

### Stage 1: Binomial reduction

Using $\binom{2p}{p} = 2\binom{2p-1}{p-1}$ and the factorization $\binom{2p-1}{p-1} \cdot (p-1)! = \prod_{k=1}^{p-1}(p+k)$, the theorem reduces to showing

$$p^3 \;\Big|\; \prod_{k=1}^{p-1}(p+k) - (p-1)!$$

### Stage 2: First-order expansion

An inductive lemma (`prod_shift_expansion`) expands the shifted product to first order:

$$\prod_{k=1}^{p-1}(p+k) - (p-1)! = p \cdot S_1 + p^2 \cdot R$$

where $S_1 = \sum_{j=1}^{p-1} (p-1)!/j$.

### Stage 3: Harmonic sum divisibility

The key lemma `harmonic_sum_dvd_sq` proves $p^2 \mid S_1$ for $p \geq 5$ via:
- Pairing terms under the involution $j \mapsto p - j$ to extract one factor of $p$
- Power sum vanishing in $\mathbb{Z}/p\mathbb{Z}$ (with $k = p-3$) for the second factor

This yields $p^3 \mid p \cdot S_1$, reducing the problem to $p \mid R$.

### Stage 4: Second-order expansion

An inductive second-order expansion (`prod_shift_expansion_2`) identifies:

$$R = e_2(\{1, \ldots, p-1\}) + p \cdot T$$

where $e_2$ is the second elementary symmetric product. This reduces the problem to $p \mid e_2$.

### Stage 5: Divisibility of $e_2$

The lemma `p_dvd_e2_prod` proves $p \mid e_2(\{1, \ldots, p-1\})$ by working in $\mathbb{Z}/p\mathbb{Z}$:
- Wilson's theorem and Fermat's little theorem reduce each term to $-i^{p-2} j^{p-2}$
- The algebraic identity $(\sum f)^2 = \sum f^2 + 2\sum_{i<j} f_i f_j$ relates $e_2$ to power sums
- Power sum vanishing with $k = p-2$ and $k = p-3$ closes the proof

### Final assembly

`wolstenholme_binom` combines all stages, using coprimality $\gcd(p^3, (p-1)!) = 1$ to lift the divisibility to the binomial coefficient.

## Key Lean declarations

| Declaration | Role |
|---|---|
| `sum_pow_Icc_zmod_eq_zero` | $\sum_{j=1}^{p-1} j^k = 0$ in $\mathbb{Z}/p\mathbb{Z}$ for $1 \leq k \leq p-2$ |
| `sum_pow_dvd` | $p \mid \sum_{j=1}^{p-1} j^k$ in $\mathbb{Z}$ (lift from ZMod) |
| `harmonic_sum_dvd_sq` | $p^2 \mid \sum (p-1)!/j$ for $p \geq 5$ |
| `prod_shift_expansion` | First-order expansion of $\prod(d+k) - \prod k$ |
| `prod_shift_expansion_2` | Second-order expansion with $e_2$ coefficient |
| `e2_prod_cons` | Recurrence for $e_2$ under `Finset.cons` |
| `p_dvd_e2_prod` | $p \mid e_2(\{1,\ldots,p-1\})$ |
| `prod_shift_mod_cube` | $p^3 \mid \prod(p+k) - (p-1)!$ |
| `wolstenholme_binom` | $\binom{2p}{p} \equiv 2 \pmod{p^3}$ |

## Key Mathlib dependencies

- `ZMod.wilsons_lemma` --- $(p-1)! \equiv -1 \pmod{p}$
- `ZMod.pow_card_sub_one_eq_one` --- Fermat's little theorem in $\mathbb{Z}/p\mathbb{Z}$
- `Finset.mul_prod_erase` --- $a \cdot \prod_{k \in s \setminus \{a\}} f(k) = \prod_{k \in s} f(k)$
- `Finset.cons_induction` --- structural induction on finite sets
- `Finset.sum_filter_add_sum_filter_not` --- partition of finite sums

## Discovery process

The proof was discovered through a collaboration between three agents:

1. **Deep Vision** --- a relational analogy engine that matches proof states against a library of 217,000 Mathlib-extracted examples, pruning the tactic search space via structural similarity (not surface syntax). Built on principles from [Fluid Concepts & Creative Analogies](https://en.wikipedia.org/wiki/Fluid_Concepts_and_Creative_Analogies) (Hofstadter, 1995).
2. **Human direction** --- decomposed the problem when automated search hit diminishing returns, choosing when to switch from exploration to direct proof.
3. **Claude Code** --- wrote the Finset manipulation proofs and number-theoretic arguments where structural matching alone could not close goals.

The effective pattern was *exploration by analogy, closure by understanding*: machine for breadth, human for decomposition, LLM for depth.

## Deep Vision vs. Deep Neural Networks

Deep Vision is the technology behind ARGO LABORATORY's entry to [Chollet's ARC-AGI](https://arcprize.org/) challenge. It represents a fundamentally different paradigm from deep learning:

| | **Deep Vision** | **Deep Neural Networks** |
|---|---|---|
| **Explainability** | Full step-by-step trace: which relations matched, which entities corresponded, why a particular analogy was chosen. Can explain to any judge why a decision was made --- and what to change to get a different outcome. | Black box. Gradient-based attribution methods (SHAP, LIME) are post-hoc approximations, not the actual reasoning path. |
| **Efficiency** | < $0.01 per task suite. Runs in a browser, in JavaScript, on a CPU, on a phone, in airplane mode. The NP-hard matching runs on commodity hardware --- a MacBook Air's GPU found this proof of Wolstenholme's theorem. | $2+ per task suite (frontier models). Requires data-center GPUs, high-bandwidth interconnects, megawatts of power. |
| **Representation** | Emergent and distributed. The system *crafts* its representation as it studies each problem --- entities, relations, and correspondences emerge from the structure of the specific situation. | Fixed. Representations are learned once during training and frozen at inference. The network cannot restructure its representation for a novel problem. |
| **Paradigm** | Relational analogy as cognition. Intelligence is perceiving shared relational structure across superficially different situations (Hofstadter, 1995). Domain-independent: the same matching engine handles chess, theorem proving, and ARC-AGI tasks. | Statistical pattern completion. Intelligence is next-token prediction over massive corpora. Domain generality comes from scale, not from architectural principles. |
| **Accessibility** | Fluid general intelligence in your pocket, regardless of who you are, where you live, or what you can afford. Runs offline, on-device, no API keys, no subscriptions, no data leaving the device. | Controlled by a handful of data-center owners. Requires internet, API access, and per-token payment. Concentrates capability in the hands of those who can afford the infrastructure. |

## Building

Requires Lean 4 and Mathlib. The formalization is a single self-contained file with one import:

```lean
import Mathlib
```

## Citation

```bibtex
@article{linhares2026wolstenholme,
  title   = {Deep Vision: A Formal Proof of Wolstenholme's Theorem in {Lean}~4},
  author  = {Linhares, Alexandre and {Deep Vision AGI} and {Claude Code}},
  year    = {2026},
  month   = {April},
  publication = {Argolab.org Report for Dissemination}
}
```

## Authors

- **Alexandre Linhares** (alexandre@linhares.ltd)
- **Deep Vision AGI**
- **Claude Code**

## License

See repository for license details.
