Require Hash.Sha256 Extraction.
Extraction Language OCaml.
Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive sumbool => "bool" [ "true" "false" ].
Extract Inductive sumor => "option" [ "Some" "None" ].
Extraction "sha256.ml" Sha256.sha256_string.

