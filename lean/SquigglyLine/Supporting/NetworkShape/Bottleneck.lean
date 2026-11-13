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

The helper `image_label_eq` says that the labels of a flock the network gets
right are read off the places after the early layers.
-/
import SquigglyLine.Networks.MarkovChains

namespace SquigglyLine

variable {State Label : Type*}

/-- **Different labels must stay apart.** If the network is right on `input`
and on `other_input`, and some layer puts them at the same place, they have the
same label. -/
theorem label_eq_of_merged
    (early_layers : LayerStack State)
    (late_layers : LayerStack State)
    (readout : State → Label)
    (label : State → Label)
    {input : State}
    {other_input : State}
    (right_on_input :
      readout (RUN_LAYERS (early_layers ++ late_layers) input)
        = label input)
    (right_on_other_input :
      readout (RUN_LAYERS (early_layers ++ late_layers) other_input)
        = label other_input)
    (merged_after_early :
      RUN_LAYERS early_layers input = RUN_LAYERS early_layers other_input) :
    let input_label := label input
    let other_label := label other_input
    input_label = other_label := by
  unfold_named_pieces
  have merged_after_all :
      RUN_LAYERS (early_layers ++ late_layers) input
        = RUN_LAYERS (early_layers ++ late_layers) other_input :=
    merged_stays_merged early_layers late_layers merged_after_early
  -- The network's answer comes from the place after all layers, and the two
  -- inputs share that place.
  rw [← right_on_input, ← right_on_other_input, merged_after_all]

/-- The labels of a flock the network gets right are read off the places it
occupies after the early layers. -/
theorem image_label_eq
    [DecidableEq State]
    [DecidableEq Label]
    (early_layers : LayerStack State)
    (late_layers : LayerStack State)
    (readout : State → Label)
    (label : State → Label)
    (flock : Finset State)
    (network_is_right : ∀ input ∈ flock,
      readout (RUN_LAYERS (early_layers ++ late_layers) input)
        = label input) :
    let labels_of_flock    := flock.image label
    let places_after_early := flock.image (RUN_LAYERS early_layers)
    let labels_read_off    :=
      places_after_early.image (readout ∘ RUN_LAYERS late_layers)
    labels_of_flock = labels_read_off := by
  unfold_named_pieces
  have run_append :
      RUN_LAYERS (early_layers ++ late_layers)
        = RUN_LAYERS late_layers ∘ RUN_LAYERS early_layers :=
    runLayers_append early_layers late_layers
  rw [Finset.image_image]
  refine Finset.image_congr fun input input_in_flock => ?_
  simp only [← network_is_right input (Finset.mem_coe.mp input_in_flock),
    run_append, Function.comp_apply]

/-- **The lower wall.** Every layer keeps at least as many places as there are
labels. -/
theorem card_image_label_le
    [DecidableEq State]
    [DecidableEq Label]
    (early_layers : LayerStack State)
    (late_layers : LayerStack State)
    (readout : State → Label)
    (label : State → Label)
    (flock : Finset State)
    (network_is_right : ∀ input ∈ flock,
      readout (RUN_LAYERS (early_layers ++ late_layers) input)
        = label input) :
    let places_after_early := flock.image (RUN_LAYERS early_layers)
    let label_count := (flock.image label).card
    let place_count := places_after_early.card
    label_count ≤ place_count := by
  unfold_named_pieces
  have labels_eq :
      flock.image label
        = (flock.image (RUN_LAYERS early_layers)).image
            (readout ∘ RUN_LAYERS late_layers) :=
    image_label_eq early_layers late_layers readout label flock
      network_is_right
  -- The labels are the image of the places, and an image is never bigger.
  rw [labels_eq]
  exact Finset.card_image_le

/-- **The bottleneck.** After any layer of a network that gets every label
right, the flock occupies at least as many places as there are labels and at
most as many as there are inputs. -/
theorem bottleneck
    [DecidableEq State]
    [DecidableEq Label]
    (early_layers : LayerStack State)
    (late_layers : LayerStack State)
    (readout : State → Label)
    (label : State → Label)
    (flock : Finset State)
    (network_is_right : ∀ input ∈ flock,
      readout (RUN_LAYERS (early_layers ++ late_layers) input)
        = label input) :
    let places_after_early := flock.image (RUN_LAYERS early_layers)
    let label_count := (flock.image label).card
    let place_count := places_after_early.card
    let input_count := flock.card
    let at_least_labels := label_count ≤ place_count
    let at_most_inputs  := place_count ≤ input_count
    at_least_labels ∧ at_most_inputs := by
  unfold_named_pieces
  exact ⟨card_image_label_le early_layers late_layers readout label flock
    network_is_right, Finset.card_image_le⟩

/-- **Full compression.** If a layer has exactly as many places as there are
labels, two inputs share a place there exactly when they share a label. -/
theorem merged_iff_label_eq
    [DecidableEq State]
    [DecidableEq Label]
    (early_layers : LayerStack State)
    (late_layers : LayerStack State)
    (readout : State → Label)
    (label : State → Label)
    (flock : Finset State)
    (network_is_right : ∀ input ∈ flock,
      readout (RUN_LAYERS (early_layers ++ late_layers) input)
        = label input)
    (as_many_places_as_labels :
      (flock.image (RUN_LAYERS early_layers)).card = (flock.image label).card)
    {input : State}
    {other_input : State}
    (input_in_flock : input ∈ flock)
    (other_input_in_flock : other_input ∈ flock) :
    let merged     := RUN_LAYERS early_layers input
                        = RUN_LAYERS early_layers other_input
    let same_label := label input = label other_input
    merged ↔ same_label := by
  unfold_named_pieces
  refine ⟨label_eq_of_merged early_layers late_layers readout label
    (network_is_right input input_in_flock)
    (network_is_right other_input other_input_in_flock), fun same_label => ?_⟩
  have labels_eq := image_label_eq early_layers late_layers readout label
    flock network_is_right
  -- The read-out map has as many places as labels, so it cannot merge two
  -- places: it is injective on them.
  have readout_injective : Set.InjOn (readout ∘ RUN_LAYERS late_layers)
      (flock.image (RUN_LAYERS early_layers) : Set State) :=
    Finset.card_image_iff.mp (by rw [← labels_eq, as_many_places_as_labels])
  have input_readout : readout (RUN_LAYERS late_layers
      (RUN_LAYERS early_layers input)) = label input := by
    simpa only [runLayers_append, Function.comp_apply] using
      network_is_right input input_in_flock
  have other_readout : readout (RUN_LAYERS late_layers
      (RUN_LAYERS early_layers other_input)) = label other_input := by
    simpa only [runLayers_append, Function.comp_apply] using
      network_is_right other_input other_input_in_flock
  refine readout_injective
    (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ input_in_flock))
    (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ other_input_in_flock)) ?_
  show readout (RUN_LAYERS late_layers (RUN_LAYERS early_layers input))
    = readout (RUN_LAYERS late_layers (RUN_LAYERS early_layers other_input))
  rw [input_readout, other_readout, same_label]

end SquigglyLine
