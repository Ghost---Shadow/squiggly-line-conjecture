# Literature Survey: Squiggly Line Conjecture

> **Note.** This survey was written while the conjecture was still open, as
> related work for a paper draft that has since been removed. Several of the
> empirical claims it originally related to this literature (the α ≈ 0.42 power
> law, dimension independence, the quantum extension) turned out to be
> measurement artifacts; see [`RESOLUTION.md`](RESOLUTION.md). The "Relation to
> this project" notes below have been revised accordingly. The citations
> themselves are kept as the record of related work.

## 0. Most directly relevant

- **Hanin, Jeong & Rolnick (2022) - "Deep ReLU Networks Preserve Expected Length" (ICLR 2022)** - Shows that, at standard initialization, deep ReLU networks preserve the expected length of an input curve: depth and width do not make the output curve longer in expectation.

**Relation to this project:** This was taken to undercut the conjecture, since the original intuition was "longer curve, more chances to pass near a point". It does not undercut the resolved result, because arc length turned out not to be the mechanism: a straight line stretched to the same arc length as a squiggly curve does not reproduce the distance reduction. What matters is how the length is spread across the domain ([`RESOLUTION.md §2`](RESOLUTION.md)).

## 1. Lottery Ticket Hypothesis & Initialization

**Core Papers:**
- **Frankle & Carbin (2019) - "The Lottery Ticket Hypothesis: Finding Sparse, Trainable Neural Networks" (ICLR 2019)** - Dense, randomly-initialized, feed-forward networks contain subnetworks ("winning tickets") that - when trained in isolation - reach test accuracy comparable to the original network in a similar number of iterations.

**Extensions & Follow-ups:**
- **Zhou et al. (2019) - "Deconstructing lottery tickets: Zeros, signs, and the supermask" (NeurIPS 2019)** - Shows it is the sign in the original initialization, not the magnitude of the weights, that is crucial to the performance of LT networks
- **Chen et al. (2021) - "The Elastic Lottery Ticket Hypothesis" (NeurIPS 2021)** - Winning tickets found from different networks of the same model family can be stretched or squeezed into subnetworks for deeper or shallower networks
- **Chen et al. (2021) - "A Unified Lottery Ticket Hypothesis for Graph Neural Networks" (ICML 2021)**

**Relation to this project:** The original hope was that geometric coverage explains why some initializations are luckier. The resolution shows coverage does not reduce initial regression loss, so it cannot be that explanation. Whether coverage relates to *reachability* (how far parameters must travel from initialization) is still open ([`RESOLUTION.md §6`](RESOLUTION.md)).

## 2. Neural Tangent Kernel (NTK) & Width Scaling

**Foundation:**
- **Jacot et al. (2018) - "Neural Tangent Kernel: Convergence and Generalization in Neural Networks" (NeurIPS 2018)** - In the infinite-width limit the NTK converges to an explicit limiting kernel and stays constant during training

**Width Scaling Studies:**
- **Liu et al. (2020) - "On the linearity of large non-linear models: when and why the tangent kernel is constant" (NeurIPS 2020)** - Relates the "transition to linearity" to the scaling of the Hessian norm with width
- **Nguyen et al. (2021) - "Tight Bounds on the Smallest Eigenvalue of the Neural Tangent Kernel for Deep ReLU Networks" (ICML 2021)**

## 3. Overparameterization Theory

- **Allen-Zhu et al. (2019) - "Learning and generalization in overparameterized neural networks, going beyond two layers" (NeurIPS 2019)**
- **Subquadratic Overparameterization for Shallow Neural Networks (NeurIPS 2021)** - Discusses width scaling quadratically with the number of training data under standard initialization

## 4. Double Descent & Benign Overfitting

- **Nakkiran et al. (2019) - "Deep Double Descent: Where Bigger Models and More Data Hurt" (ICLR 2020)** - A variety of modern deep learning tasks exhibit a "double-descent" phenomenon in model size
- **Benign overfitting in deep neural networks under lazy training (ICML 2023)**
- **NeurIPS 2023 Tutorial: Reconsidering Overfitting in the Age of Overparameterized Models**

## 5. Scaling Laws

- **Kaplan et al. (2020) - "Scaling Laws for Neural Language Models"** - Loss scales as a power law with model size, dataset size, and compute
- **Bahri, Dyer, Kaplan, Lee & Sharma (2024) - "Explaining Neural Scaling Laws" (PNAS 2024)** - Identifies variance-limited and resolution-limited scaling regimes with respect to dataset size and parameter count

**Relation to this project:** The α ≈ 0.42 power law from `scripts/relu_chain.py` was once compared to this literature. It is signal attenuation under Xavier initialization, not a scaling law ([`RESOLUTION.md §4`](RESOLUTION.md)).

## 6. Random Matrix Theory

- **Pennington & Worah (2017) - "Nonlinear random matrix theory for deep learning" (NIPS 2017)** - Incorporates pointwise nonlinearities into the moments method of random matrix theory
- **Louart et al. (2017) - "A Random Matrix Approach to Neural Networks"** - Studies the Gram random matrix model for analyzing neural networks
- **ICML 2021 tutorial on Random Matrix Theory and Machine Learning**

## 7. Activation Patterns & Network Expressivity

- **Hanin & Rolnick (2019) - "Deep ReLU Networks Have Surprisingly Few Activation Patterns" (NeurIPS 2019)** - The average number of activation patterns for ReLU networks at initialization is bounded by the total number of neurons raised to the input dimension
- **Hartmann et al. (2021) - "Studying the Evolution of Neural Activation Patterns During Training"**

## 8. Neural Networks and Quantum States

- **Infinite Neural Network Quantum States (2023)** - Uses neural networks to represent quantum wavefunctions
- **Ab initio quantum chemistry with neural-network wavefunctions (Nature Reviews Chemistry)**
- **Carleo & Troyer (2017) - Neural Quantum States** - Neural networks for quantum many-body problems

**Relation to this project:** The quantum extension (coverage ∝ √E) is circular and contradicted by its own script; it should not be revived ([`RESOLUTION.md §6`](RESOLUTION.md)).

## 9. Dimpled Manifold Theory & Decision Boundary Geometry

- **Shamir et al. (2021) - "The Dimpled Manifold Model of Adversarial Examples in Machine Learning"** - Proposes that training has a fast "clinging" phase, in which the decision boundary approaches the low-dimensional data manifold, followed by a slow "dimpling" phase

**Related Manifold Work:**
- **Colah (2014) - "Neural Networks, Manifolds, and Topology"** - Blog post on how neural networks untangle topological structures
- **Manifold Hypothesis** - Many high-dimensional real-world data sets lie near low-dimensional manifolds

## 10. Geometric Deep Learning

- **Geometric Intelligence Lab publications** - Geometric signatures in neural networks
- **NeurIPS 2022 Workshop: Symmetry and Geometry in Neural Representations**

## References

1. **Frankle, J. and Carbin, M.** "The lottery ticket hypothesis: Finding sparse, trainable neural networks." *ICLR*, 2019.

2. **Jacot, A., Gabriel, F., and Hongler, C.** "Neural tangent kernel: Convergence and generalization in neural networks." *NeurIPS*, 2018.

3. **Kaplan, J., McCandlish, S., Henighan, T., et al.** "Scaling laws for neural language models." *arXiv preprint arXiv:2001.08361*, 2020.

4. **Bahri, Y., Dyer, E., Kaplan, J., Lee, J., and Sharma, U.** "Explaining neural scaling laws." *PNAS*, 2024.

5. **Hanin, B. and Rolnick, D.** "Deep ReLU networks have surprisingly few activation patterns." *NeurIPS*, 2019.

6. **Hanin, B., Jeong, R., and Rolnick, D.** "Deep ReLU networks preserve expected length." *ICLR*, 2022.

7. **Carleo, G. and Troyer, M.** "Solving the quantum many-body problem with artificial neural networks." *Science*, 2017.

8. **Nakkiran, P., Kaplun, G., Bansal, Y., et al.** "Deep double descent: Where bigger models and more data hurt." *ICLR*, 2020.

9. **Pennington, J. and Worah, P.** "Nonlinear random matrix theory for deep learning." *NIPS*, 2017.

10. **Allen-Zhu, Z., Li, Y., and Liang, Y.** "Learning and generalization in overparameterized neural networks, going beyond two layers." *NeurIPS*, 2019.

11. **Zhou, H., Lan, J., Liu, R., and Yosinski, J.** "Deconstructing lottery tickets: Zeros, signs, and the supermask." *NeurIPS*, 2019.

12. **Chen, X., Cheng, Y., Wang, S., et al.** "The elastic lottery ticket hypothesis." *NeurIPS*, 2021.

13. **Shamir, A., Melamed, O., and BenShmuel, O.** "The dimpled manifold model of adversarial examples in machine learning." *arXiv preprint arXiv:2106.10151*, 2021.
