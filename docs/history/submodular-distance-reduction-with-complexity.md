# Proof: Submodular Distance Reduction with Complexity

> **Historical.** Written before the conjecture was resolved. Empirical claims
> here are superseded by [`docs/RESOLUTION.md`](../RESOLUTION.md). Kept as a record of
> how the idea developed.

## Setup

**Given:** Expected distance scales with uncovered volume fraction:
$$\mathbb{E}[\text{dist}(p, f)] \sim \left(\frac{V_{\text{uncovered}}}{V_{\text{total}}}\right)^{1/d}$$

**Coverage volume:** $V_{\text{covered}}(f) = \min(L(f) \cdot k \cdot \epsilon^{d-1}, V_{\text{total}})$

Note the $\min$ operator - coverage saturates at $V_{\text{total}}$.

## Submodularity Derivation

### Step 1: Uncovered Volume as Function of Arc Length

$$V_{\text{uncovered}}(L) = \max(V_{\text{total}} - L \cdot k \cdot \epsilon^{d-1}, 0)$$

### Step 2: Expected Distance as Function of Arc Length

$$\mathbb{E}[\text{dist}(L)] = \left(\frac{\max(V_{\text{total}} - L \cdot k \cdot \epsilon^{d-1}, 0)}{V_{\text{total}}}\right)^{1/d}$$

Simplifying for $L < \frac{V_{\text{total}}}{k \cdot \epsilon^{d-1}}$:

$$\mathbb{E}[\text{dist}(L)] = \left(1 - \frac{L \cdot k \cdot \epsilon^{d-1}}{V_{\text{total}}}\right)^{1/d}$$

### Step 3: Marginal Benefit Analysis

Define marginal benefit of adding arc length $\Delta L$:
$$B(\Delta L | L) = \mathbb{E}[\text{dist}(L)] - \mathbb{E}[\text{dist}(L + \Delta L)]$$

Taking the derivative with respect to $L$:
$$\frac{d\mathbb{E}[\text{dist}]}{dL} = -\frac{1}{d} \cdot \left(1 - \frac{L \cdot k \cdot \epsilon^{d-1}}{V_{\text{total}}}\right)^{\frac{1}{d}-1} \cdot \frac{k \cdot \epsilon^{d-1}}{V_{\text{total}}}$$

### Step 4: Second Derivative (Proving Diminishing Returns)

$$\frac{d^2\mathbb{E}[\text{dist}]}{dL^2} = \frac{1-d}{d^2} \cdot \left(1 - \frac{L \cdot k \cdot \epsilon^{d-1}}{V_{\text{total}}}\right)^{\frac{1}{d}-2} \cdot \left(\frac{k \cdot \epsilon^{d-1}}{V_{\text{total}}}\right)^2$$

Since $d > 1$ (we're in at least 2D), we have $\frac{1-d}{d^2} < 0$, but the overall expression is **positive** because $\frac{1}{d}-2 < 0$ makes the middle term flip sign.

This means $\left|\frac{d\mathbb{E}[\text{dist}]}{dL}\right|$ is **decreasing** - each additional unit of arc length provides less distance reduction.

### Step 5: Submodularity Property

For arc lengths $L_1 < L_2$ and increment $\Delta L$:

$$B(\Delta L | L_1) > B(\Delta L | L_2)$$

This is the definition of submodularity: **adding complexity to a simple function helps more than adding the same complexity to an already complex function**.

### Step 6: Saturation Limit

As $L \to \frac{V_{\text{total}}}{k \cdot \epsilon^{d-1}}$:

$$\mathbb{E}[\text{dist}(L)] \to 0$$

But this requires $L \to \infty$ as $\epsilon \to 0$, showing that perfect coverage requires infinite complexity.

## Key Results

1. **Initial gains are large**: When $L \approx 0$, small increases in complexity dramatically reduce distance

2. **Diminishing returns**: As $L$ increases, the marginal benefit decreases following:
   $$\frac{dB}{dL} \propto \left(1 - \frac{L \cdot k \cdot \epsilon^{d-1}}{V_{\text{total}}}\right)^{\frac{1}{d}-2}$$

3. **Practical saturation**: Most benefit achieved when $V_{\text{covered}} \approx 0.9 \cdot V_{\text{total}}$

4. **Never fully saturates**: Even infinite complexity leaves some expected distance (the $\epsilon$ neighborhood)

## Implications

- Early complexity additions (first few Fourier modes, initial neural network layers) provide the most benefit
- Later additions provide marginal improvements
- There's a "sweet spot" of complexity beyond which gains are minimal
- This explains why overparameterized models don't infinitely improve performance
