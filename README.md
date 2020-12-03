# algebraic-free-abstract-montague

## Usage

Example (see [Fragment.hs](https://github.com/juliangrove/algebraic-free-abstract-montague/blob/main/src/Fragment.hs)): 'Every dog who chased a cat caught it.'

Print:

	`test1 = runSentence @Print @Entity @Entity $ every (return dog <| (return who |> (return chase |> bind (some cat)))) <| (return catch |> it)`

Evaluate:

	`test2 = runSentence @Eval @Entity @Entity $ every (return dog <| (return who |> (return chase |> bind (some cat)))) <| (return catch |> it)`

Export to [Coq](https://coq.inria.fr/):

	`test3 = runSentence @CoqTerm @Entity @Entity $ every (return dog <| (return who |> (return chase |> bind (some cat)))) <| (return catch |> it)`

## Semantic inference

See [Inference.v](https://github.com/juliangrove/algebraic-free-abstract-montague/blob/main/Inference.v) for an example entailment proof.
