/-
The information bottleneck, by counting.

Send a finite flock through the layers and count the distinct places it
occupies after each one. `readout` turns the last layer's place into an answer.

* `label_eq_of_merged` : a network that is right on two inputs cannot merge
  them at any layer unless they have the same label.
* `card_image_label_le` : so every layer keeps at least as many places as
  there are labels.
* `bottleneck` : the count lies between the number of labels and the number
  of inputs. (It never goes up: `card_image_runLayers_append_le`.)
* `merged_iff_label_eq` : a layer squeezed down to exactly as many places as
  labels merges two inputs exactly when they share a label.
-/
import SquigglyLine.Networks.MarkovChains

namespace SquigglyLine

variable {α β : Type*}

/-- **Different labels must stay apart.** If the network is right on `x` and on `y`, and
some layer puts them at the same place, they have the same label. -/
theorem label_eq_of_merged (early late : List (α → α)) (readout label : α → β) {x y : α}
    (hx : readout (runLayers (early ++ late) x) = label x)
    (hy : readout (runLayers (early ++ late) y) = label y)
    (h : runLayers early x = runLayers early y) : label x = label y := by
  rw [← hx, ← hy, merged_stays_merged early late h]

/-- The labels of a flock the network gets right are read off the places it occupies after
the early layers. -/
theorem image_label_eq [DecidableEq α] [DecidableEq β] (early late : List (α → α))
    (readout label : α → β) (flock : Finset α)
    (hfit : ∀ x ∈ flock, readout (runLayers (early ++ late) x) = label x) :
    flock.image label = (flock.image (runLayers early)).image (readout ∘ runLayers late) := by
  rw [Finset.image_image]
  refine Finset.image_congr fun x hx => ?_
  simp only [← hfit x (Finset.mem_coe.mp hx), runLayers_append, Function.comp_apply]

/-- **The lower wall.** Every layer keeps at least as many places as there are labels. -/
theorem card_image_label_le [DecidableEq α] [DecidableEq β] (early late : List (α → α))
    (readout label : α → β) (flock : Finset α)
    (hfit : ∀ x ∈ flock, readout (runLayers (early ++ late) x) = label x) :
    (flock.image label).card ≤ (flock.image (runLayers early)).card := by
  rw [image_label_eq early late readout label flock hfit]
  exact Finset.card_image_le

/-- **The bottleneck.** After any layer of a network that gets every label right, the flock
occupies at least as many places as there are labels and at most as many as there are
inputs. -/
theorem bottleneck [DecidableEq α] [DecidableEq β] (early late : List (α → α))
    (readout label : α → β) (flock : Finset α)
    (hfit : ∀ x ∈ flock, readout (runLayers (early ++ late) x) = label x) :
    (flock.image label).card ≤ (flock.image (runLayers early)).card
      ∧ (flock.image (runLayers early)).card ≤ flock.card :=
  ⟨card_image_label_le early late readout label flock hfit, Finset.card_image_le⟩

/-- **Full compression.** If a layer has exactly as many places as there are labels, two
inputs share a place there exactly when they share a label. -/
theorem merged_iff_label_eq [DecidableEq α] [DecidableEq β] (early late : List (α → α))
    (readout label : α → β) (flock : Finset α)
    (hfit : ∀ x ∈ flock, readout (runLayers (early ++ late) x) = label x)
    (hcard : (flock.image (runLayers early)).card = (flock.image label).card) {x y : α}
    (hx : x ∈ flock) (hy : y ∈ flock) :
    runLayers early x = runLayers early y ↔ label x = label y := by
  refine ⟨label_eq_of_merged early late readout label (hfit x hx) (hfit y hy), fun hlab => ?_⟩
  have himage := image_label_eq early late readout label flock hfit
  have hinj : Set.InjOn (readout ∘ runLayers late) (flock.image (runLayers early) : Set α) :=
    Finset.card_image_iff.mp (by rw [← himage, hcard])
  have hx' : readout (runLayers late (runLayers early x)) = label x := by
    simpa only [runLayers_append, Function.comp_apply] using hfit x hx
  have hy' : readout (runLayers late (runLayers early y)) = label y := by
    simpa only [runLayers_append, Function.comp_apply] using hfit y hy
  refine hinj (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hx))
    (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hy)) ?_
  show readout (runLayers late (runLayers early x)) = readout (runLayers late (runLayers early y))
  rw [hx', hy', hlab]

end SquigglyLine
