/-
Root module for `SelfAttention` — T2 (Kim–Papamakarios–Mnih 2021).  The attention
sensitivity constant `L_attn` behind `attention.linear_dominance` (softmax-free,
the clean target) and `attention.fixed_pattern` (softmax).

See `SelfAttention/README.md` and prose/self-attention-lipschitz.md.
-/

import SelfAttention.LinearDominance
import SelfAttention.LinearDominanceBlock
import SelfAttention.FixedPattern
import SelfAttention.FixedPatternBlock
import SelfAttention.ConcreteGlue
import SelfAttention.FixedPatternConcrete
import SelfAttention.LinearDominanceConcrete
