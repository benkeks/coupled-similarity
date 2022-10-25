# Computing Coupled Similarity

This repository contains sources and proofs related to the following two papers:

- Bisping, B., Nestmann, U. (2019). [Computing Coupled Similarity.](https://doi.org/10.1007/978-3-030-17462-0_14) TACAS 2019. Lecture Notes in Computer Science 11427.
- Bisping, B., Nestmann, U. & Peters, K. [Coupled similarity: The first 32 years](https://doi.org/10.1007/s00236-019-00356-4). Acta Informatica 57, (2020).

Coupled similarity is a notion of equivalence for systems with internal actions. It has outstanding applications in contexts where internal choices must transparently be distributed in time or space, for example, in process calculi encodings or in action refinements. No tractable algorithms for the computation of coupled similarity have been proposed up to now. Accordingly, there has not been any tool support.

Our TACAS 2019 publication presents a game-theoretic algorithm to compute coupled similarity, running in cubic time and space with respect to the number of states in the input transition system. We show that one cannot hope for much better because deciding the coupled simulation preorder is at least as hard as deciding the weak simulation preorder.

- `isabelle/` contains machine-checkable proofs using Isabelle/HOL on the theoretical key results concerning game characterization, reducibility, and polynomial algorithm solution.
* `code/flink/` provides source code of an experimental Scala implementation of the game algorithm using the Apache Flink framework for scalable parallelized computations.
* `code/` moreover contains a webtool for trying out the algorithms, which runs on <https://coupledsim.bbisping.de/>.
* `thesis/` assembles the source files of Benjamin Bisping's master thesis. The [PDF](bisping_computingCoupledSimilarity_thesis.pdf) is included as well.

An artifact packaging most of this including all code dependencies is on [Figshare](https://doi.org/10.6084/m9.figshare.7831382.v1).

The algorithm of this project has been integrated into [mCRL2](https://github.com/mCRL2org/mCRL2) by [PR 1619](https://github.com/mCRL2org/mCRL2/pull/1619).
