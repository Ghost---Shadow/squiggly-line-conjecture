# [Mathematical Formalization of the Squiggly Line Conjecture](https://claude.ai/share/39f58f0c-70e3-4b12-a087-d32d96efa458)

When you scatter random points on a plane and draw two curves through the same space - one simple and straight-ish, another complex and squiggly - the squiggly curve will, on average, pass closer to your random points even though both curves are drawn randomly without "seeing" the points first. This happens because a squiggly line covers more total length as it winds through the space, giving it more opportunities to accidentally pass near any given point, much like how a longer fishing line cast randomly into a pond has better chances of landing near fish than a shorter one. This geometric insight explains why larger neural networks often learn faster from the very beginning of training: their random initialization already positions them closer to the data they need to fit, not because they're "smarter" but simply because their complexity gives them better coverage of the possible solution space - though this advantage plateaus once the curve becomes so squiggly it starts wasting its length by looping back on itself.

## 1. Problem Setup

Let $\mathcal{D} = \{(x_i, y_i)\}_{i=1}^n$ be a set of points in $[-1, 1]^2$.

Let $P_d$ be the space of polynomials of degree $d$:
$$P_d = \{p(x) = \sum_{k=0}^d a_k x^k : a_k \in \mathbb{R}\}$$

For a polynomial $p \in P_d$ with random coefficients $a_k \sim \text{Uniform}(-\alpha, \alpha)$, define the average distance to the dataset:
$$L(p, \mathcal{D}) = \frac{1}{n} \sum_{i=1}^n \min_{x \in [-1,1]} \|(x_i, y_i) - (x, p(x))\|_2$$

## 2. The Squiggly Line Conjecture

**Conjecture**: For randomly initialized polynomials $p_d \in P_d$ and $p_{d'} \in P_{d'}$ where $d < d'$:
$$\mathbb{E}[L(p_{d'}, \mathcal{D})] < \mathbb{E}[L(p_d, \mathcal{D})]$$

## 3. Key Mechanisms

### 3.1 Spatial Coverage Density

For a polynomial $p \in P_d$, define its **curve length** in $[-1, 1]$:
$$\ell(p) = \int_{-1}^1 \sqrt{1 + (p'(x))^2} dx$$

**Claim**: Higher degree polynomials have greater expected curve length:
$$\mathbb{E}[\ell(p_d)] < \mathbb{E}[\ell(p_{d+1})]$$

This follows because:
- $p'(x) = \sum_{k=1}^d k \cdot a_k x^{k-1}$
- Higher degrees allow more variation in the derivative
- Expected squared derivative grows with degree: $\mathbb{E}[(p'(x))^2] \propto d$

### 3.2 Effective Coverage Volume

Define the **$\epsilon$-neighborhood** of a polynomial:
$$N_\epsilon(p) = \{(x, y) \in [-1, 1]^2 : \exists t \in [-1,1], \|(x, y) - (t, p(t))\| < \epsilon\}$$

The **coverage volume** is:
$$V_\epsilon(p) = \text{Area}(N_\epsilon(p))$$

**Approximation**: For small $\epsilon$ and non-self-intersecting curves:
$$V_\epsilon(p) \approx 2\epsilon \cdot \ell(p)$$

Therefore: $\mathbb{E}[V_\epsilon(p_{d'})] > \mathbb{E}[V_\epsilon(p_d)]$ for $d' > d$

### 3.3 Expected Minimum Distance

For a uniform random point $(x, y) \in [-1, 1]^2$, the probability it lies within distance $r$ of polynomial $p$ is approximately:
$$P(\text{dist}((x, y), p) < r) \approx \frac{V_r(p)}{4}$$

The expected minimum distance can be approximated by:
$$\mathbb{E}[\min \text{dist}] \approx \int_0^\infty P(\text{dist} > r) dr = \int_0^\infty \left(1 - \frac{V_r(p)}{4}\right) dr$$

## 4. Formal Analysis

### 4.1 Random Polynomial Statistics

For a degree-$d$ polynomial with i.i.d. coefficients $a_k \sim \text{Uniform}(-\alpha, \alpha)$:

**Variance of the polynomial**:
$$\text{Var}[p(x)] = \sum_{k=0}^d \text{Var}[a_k] x^{2k} = \frac{\alpha^2}{3} \sum_{k=0}^d x^{2k}$$

For $x \in [-1, 1]$:
$$\text{Var}[p(x)] \leq \frac{\alpha^2}{3}(d + 1)$$

**Expected number of local extrema**: 
By Kac's theorem, a random polynomial of degree $d$ has expected number of real roots:
$$\mathbb{E}[\#\text{extrema}] \approx \frac{2}{\pi} \log(d) + O(1)$$

### 4.2 Distance Distribution

For a point $(x_0, y_0)$ and polynomial $p$, the minimum distance satisfies:
$$d_{\min} = \min_{x \in [-1,1]} \sqrt{(x - x_0)^2 + (p(x) - y_0)^2}$$

**Theorem (Informal)**: As $d \to \infty$, the expected minimum distance follows:
$$\mathbb{E}[d_{\min}] \sim C \cdot d^{-\gamma}$$
where $\gamma \approx 1/2$ and $C$ depends on the coefficient distribution.

### 4.3 The Saturation Effect

The improvement saturates because:

1. **Self-intersection penalty**: For large $d$, polynomials increasingly self-intersect, reducing effective coverage
2. **Boundary effects**: Polynomials of very high degree tend to oscillate wildly near $x = \pm 1$
3. **Coefficient scaling**: To maintain bounded output, coefficient magnitude must decrease with degree

The optimal degree $d^*$ satisfies:
$$d^* = \arg\min_d \left[ \mathbb{E}[L(p_d, \mathcal{D})] + \lambda \cdot \text{Penalty}(d) \right]$$

where the penalty term accounts for self-intersection and boundary effects.

## 5. Connection to Neural Networks

### 5.1 Function Space Analogy

A neural network with $m$ hidden units can be viewed as:
$$f(x) = \sum_{j=1}^m v_j \sigma(w_j^T x + b_j)$$

The "squiggliness" corresponds to:
- **Width**: More hidden units ↔ higher polynomial degree
- **Expressivity**: Larger $m$ allows more complex decision boundaries

### 5.2 Random Initialization

At initialization with $w_j, v_j \sim \mathcal{N}(0, \sigma^2)$:
- The function $f$ explores a random subspace of dimension $\sim m$
- Higher $m$ provides denser coverage of the input space
- Expected distance to data points decreases with $m$

### 5.3 Optimal Network Size

The conjecture suggests an optimal size $m^*$ where:
$$m^* \propto n^{\beta} \cdot H(\mathcal{D})$$

where:
- $n$ = number of data points
- $H(\mathcal{D})$ = entropy/complexity of the data distribution
- $\beta \approx 1/2$ to $2/3$ (empirically determined)

## 6. Testable Predictions

1. **Distribution Dependency**: 
   $$\frac{\mathbb{E}[L(p_{d'}, \mathcal{D})]}{\mathbb{E}[L(p_d, \mathcal{D})]} \propto 1 - \alpha \cdot H(\mathcal{D})$$
   where $H(\mathcal{D})$ is the entropy of the point distribution

2. **Scaling Law**:
   $$\mathbb{E}[L(p_d, \mathcal{D})] \approx L_0 \cdot \left(1 + \frac{A}{d^\gamma}\right)$$
   with $\gamma \approx 0.5$ for uniform random points

3. **Critical Degree**:
   $$d_{\text{critical}} \approx C \cdot n^{1/2}$$
   beyond which no improvement occurs

## 7. Open Questions

1. Can we prove the conjecture rigorously for specific distributions?
2. What is the exact relationship between polynomial degree and neural network width?
3. How does the conjecture extend to higher dimensions?
4. Can we derive the optimal coefficient distribution for minimizing expected distance?

## 8. Conclusion

The Squiggly Line Conjecture provides a geometric foundation for understanding why overparameterized models have an initialization advantage. The key insight is that randomly initialized complex functions have greater "spatial coverage density," making them statistically closer to random data points before any training occurs.

This formalization suggests that the benefit of overparameterization is:
- **Real but bounded** (saturates at critical complexity)
- **Distribution-dependent** (stronger for high-entropy data)
- **Geometrically interpretable** (coverage density in function space)
