# Preface

This book is a guided tour of the proofs in the
[squiggly line theorem](https://github.com/Ghost---Shadow/squiggly-line-theorem)
repository. The repository holds about eighty files of machine-checked
mathematics. Read in the order the files happen to depend on each other,
they are hard to follow. This book puts them in the order of the ideas.

## Who it is for

You can read Python, and you remember school mathematics: slopes, sines,
Pythagoras, averages. That is enough. You do not need to know Lean, the
language the proofs are written in. Chapter 2 teaches as much of it as you
need, and that is not much, because the proofs here are written to be read.

## How each chapter works

1. **The idea in plain words**, with a small example you can check by hand.
2. **The statement as it is in the repository.** These are copied from the
   Lean files, not rewritten.
3. **Why it is true**, as a short argument in words that follows the steps
   of the Lean proof.
4. **Check yourself.** A few questions, with answers at the end of the
   chapter.
5. **In the repository.** Where to read the full proof and the longer notes.

## What "proved" means here

Every statement the book calls **proved** has been checked line by line by
Lean, a program built to check proofs. The whole project is rebuilt from
nothing on every change, and the build fails if a single step is left
unjustified. So you do not have to trust the author, and you do not have to
trust this book. You can trust the checker, and read the statements to see
what was checked.

A proof only covers what its statement says. Most statements here are about
simplified models, and each chapter says where the proof stops. Where
something is only measured, or only argued, the book says so.

## Who wrote it

The book has two authors. Claude, an AI model made by Anthropic, wrote
the text and the Lean proofs. Souradeep Nanda had the idea, set the
style, chose what to prove and directed the work. The proofs are checked
by Lean. The prose is not: if a sentence in this book and a Lean
statement disagree, the Lean statement is right.

## The parts

- **Part I, the theorem (chapters 1 to 7).** One picture, two distances and
  three short results. Together they give the theorem: a squigglier curve
  is closer to the data, steeper by the same factor, and no better at the
  start of training.
- **Part II, networks (chapters 8 to 12).** What the theorem means for
  neural networks: depth and folds, the distance the weights travel, the
  kernel, the lift, and layers seen as polarizers.
- **Part III, a map (chapters 13 to 16).** The handful of tools from
  parts I and II, pointed at well-known results of deep learning. Four
  short chapters, each the map of one of the parts that follow.
- **Parts IV to VII, proof by proof (chapters 17 to 46).** The same
  ground again, slowly, one topic per chapter: training, architecture,
  averages, and what a fitted model does on new inputs. This is where
  the book meets the rest of deep-learning research.
- **Chapter 47** says where the proofs stop.

## Four ways through

- **The short way.** Chapters 1 to 7. This is the theorem, start to finish.
- **If you train models.** Chapters 1, 3, 9, 10 and 13, then pick from
  part IV. Slope, travel and the one factor behind most training rules.
- **If you came for one topic.** Read chapters 1 to 12 once. After that,
  every chapter from 17 on stands on its own and says which earlier
  chapters it needs.
- **If you want everything.** Straight through.

Next: [1. Two distances](01-two-distances.md)
