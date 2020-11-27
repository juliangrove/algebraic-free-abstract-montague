# algebraic-free-abstract-montague

Example (see [Fragment.hs](https://github.com/juliangrove/algebraic-free-abstract-montague/blob/main/src/Fragment.hs)): 'Every dog who chased a cat caught it.'

Print:

`runSentence @() @Print @Entity $ every (return dog <| (return who |> (return chase |> bind (some cat)))) <| (return catch |> it)`

Evaluate:

`runSentence @() @Eval @Entity $ every (return dog <| (return who |> (return chase |> bind (some cat)))) <| (return catch |> it)`
