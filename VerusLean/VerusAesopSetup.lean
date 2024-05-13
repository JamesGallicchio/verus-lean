import Aesop

declare_aesop_rule_sets [VerusLean]

macro "verus_default_tac" : tactic =>
  `(tactic| first | (aesop (rule_sets := [VerusLean]) <;> (first | exact? | sorry)) | exact? | sorry)

macro "verus_attr" : attr => do
  `(attr|
    aesop unsafe 1% apply (rule_sets := [VerusLean])
  )
