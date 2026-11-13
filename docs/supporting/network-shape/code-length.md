# Compression: folds, code length and travel

**Proofs:** [`Depth.lean`](../../../lean/SquigglyLine/Networks/Depth.lean), [`CodeLength.lean`](../../../lean/SquigglyLine/Supporting/NetworkShape/CodeLength.lean).

Notes from 12 Nov 2026. Written before the proofs, then updated once they were
done. Each statement is marked **proved** (in
[`lean/SquigglyLine/Supporting/NetworkShape/CodeLength.lean`](../../../lean/SquigglyLine/Supporting/NetworkShape/CodeLength.lean) unless another file is named),
**recalled**, or **open**.

## The idea

There is an old view that learning is compression: to predict data well is to
be able to write it down briefly (**recalled**: Shannon 1948; Rissanen 1978).
Three parts of that view can be tied to this project. One is about counting,
one about loss, and one about distance.

Huffman coding is not among them. It is the method that builds the best code
when some outcomes are likelier than others (**recalled**: Huffman 1952). The
limit it reaches is in the second part below. The method itself is a separate
subject and is not formalised here.

## Counting: bits and folds

**A code of `b` binary digits names at most `2^b` things**
(**proved**: `card_le_two_pow_of_code`). To tell `k` things apart you need at
least `log₂ k` digits. With every outcome equally likely, that is the whole
theory of compression.

**A fold throws away one bit.** The tent layer folds the interval in half, so
an input and its mirror image give the same output
(**proved**: `tent_one_sub`), and nothing else is lost: two inputs with the
same output are equal or are mirror images
(**proved**: `eq_or_eq_one_sub_of_tent_eq`). The bit that is lost is "which
half was I in".

**So `L` folds throw away at most `L` bits.** No more than `2^L` inputs can
end up at the same output after `L` folds
(**proved**: `card_le_two_pow_of_iterate_tent_eq`). And about that many do:
all the even grid points go to zero (**proved** earlier:
`iterate_tent_dyadic`).

A layer is one binary digit. Depth is code length.

## Loss: the entropy limit

Train a model with the usual log-loss. Then its loss on a piece of data is
the number of digits it takes to write that data down with the model's help
(**recalled**: this is arithmetic coding). A better model is a shorter code.

How short can it get? Not below the entropy of the data:

```
average log-loss of any model  ≥  entropy of the data
```

(**proved**: `gibbs`.) The same inequality bounds any code at all. If the
code lengths obey the rule that every decodable code obeys, the average
length is at least the entropy (**proved**: `expected_length_ge_entropy`; the
rule is Kraft's inequality, taken as an assumption). This is the limit a
Huffman code comes within one digit of (**recalled**).

So "maximum compression" has an exact meaning for a model. It is the lowest
loss any model can reach, and it is a property of the data.

## Distance: travel is description length

To send someone a trained model you could send its weights. If they already
have the starting weights, you only need to send the change. The cost of
doing that, in the standard account, goes as the squared distance between
the two, divided by twice the square of the precision `σ`
(**recalled**: Hinton and van Camp 1993; this is the divergence between two
Gaussians of the same width, and it is the quantity in PAC-Bayes bounds).
Here that formula is taken as the definition of description length.

Then two results from this project read as statements about compression.

- **Gradient descent finds the fit that is cheapest to describe.** It reaches
  the nearest fit, so no other fit has a shorter description
  (**proved**: `descriptionLength_gradientDescent_le`).
- **A bigger model's fit is cheaper to describe.** With orthogonal features of
  strength `c`, the description length of the nearest fit is the squared
  error at the start divided by `2σ²c` (**proved**:
  `travel_sq_div_eq_of_tight`). It falls as `c` grows, and `c` grows with the
  number of parameters.

This is the squiggly line theorem's "distance to move", counted in bits. A
bigger model has more weights to describe and still needs fewer bits to say
how they changed. In the description-length view that is why a bigger model
can generalise better: a fit that takes few bits to describe cannot have
memorised much.

## What is not shown

- **Huffman's method**, and Kraft's inequality itself.
- **That log-loss is a code length.** The inequality is proved. The coding
  method that turns a model into a code of that length is recalled.
- **The Gaussian formula.** That description length goes as squared distance
  is taken as a definition. Proving it needs Gaussian measures.
- **The bound on generalisation** that follows from a short description
  (PAC-Bayes) is not derived. **open** here.
- **Units.** The entropy statements are in natural units. Divide by `log 2`
  for bits.
