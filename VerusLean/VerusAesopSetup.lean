import Aesop

declare_aesop_rule_sets [VerusLean]

macro "verus_default_tac" : tactic =>
  `(tactic| first | (aesop (rule_sets := [VerusLean]) <;> sorry) | sorry)
