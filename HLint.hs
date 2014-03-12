import "hint" HLint.HLint

infixr 5 :<

-- This affects performance
ignore "Redundant lambda"

-- This is not valid for improve
ignore "Eta reduce"

-- DeriveDataTypable noise
ignore "Unused LANGUAGE pragma"

-- They are clearer in places
ignore "Avoid lambda"
