# Proof: More Complex Curves Have Lower Expected Distance

> **Historical.** Written before the conjecture was resolved. Empirical claims
> here are superseded by [`RESOLUTION.md`](RESOLUTION.md). Kept as a record of
> how the idea developed.

## Setup

**Given:** Expected distance scales with uncovered volume fraction:
$$\mathbb{E}[\text{dist}(p, f)] \sim \left(\frac{V_{\text{uncovered}}}{V_{\text{total}}}\right)^{1/d}$$

**Define:** Coverage region of function $f$ with radius $\epsilon$:
$$C_\epsilon(f) = \{(x,y) : \text{dist}((x,y), \text{graph}(f)) \leq \epsilon\}$$

**Arc length:** $L(f) = \int_a^b \sqrt{1 + (f'(x))^2} \, dx$

## Derivation

### Step 1: Coverage Volume
The covered volume is proportional to arc length:
$$V_{\text{covered}}(f) = V(C_\epsilon(f)) = L(f) \cdot k \cdot \epsilon^{d-1}$$
where $k$ is a dimensional constant.

### Step 2: Two Functions
Consider functions $f_c$ (complex) and $f_s$ (simple) where:
$$L(f_c) > L(f_s)$$

### Step 3: Compare Covered Volumes
$$V_{\text{covered}}(f_c) = L(f_c) \cdot k \cdot \epsilon^{d-1} > L(f_s) \cdot k \cdot \epsilon^{d-1} = V_{\text{covered}}(f_s)$$

### Step 4: Convert to Uncovered Volumes
$$V_{\text{uncovered}} = V_{\text{total}} - V_{\text{covered}}$$

Therefore:
$$V_{\text{uncovered}}(f_c) = V_{\text{total}} - V_{\text{covered}}(f_c) < V_{\text{total}} - V_{\text{covered}}(f_s) = V_{\text{uncovered}}(f_s)$$

### Step 5: Apply Scaling
$$\frac{V_{\text{uncovered}}(f_c)}{V_{\text{total}}} < \frac{V_{\text{uncovered}}(f_s)}{V_{\text{total}}}$$

Since $x^{1/d}$ is monotonically increasing:
$$\left(\frac{V_{\text{uncovered}}(f_c)}{V_{\text{total}}}\right)^{1/d} < \left(\frac{V_{\text{uncovered}}(f_s)}{V_{\text{total}}}\right)^{1/d}$$

### Step 6: Final Result
$$\boxed{\mathbb{E}[\text{dist}(p, f_c)] < \mathbb{E}[\text{dist}(p, f_s)]}$$

## Summary
**Greater complexity → Greater arc length → Greater covered volume → Less uncovered volume → Lower expected distance**