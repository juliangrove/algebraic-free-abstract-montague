module Model where

data Entity = E1  | E2  | E3  | E4  | E5  | E6
            | E7  | E8  | E9  | E10 | E11 | E12
            | E13 | E14 | E15 | E16 | E17 | E18
            | E19 | E20 | E21 | E22 | E23 | E24
            | E25 | E26 | E27 | E28 | E29 | E30
            deriving (Show, Eq, Bounded, Enum)

entities :: [Entity]
entities = [minBound..maxBound]
