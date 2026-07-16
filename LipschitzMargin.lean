/-
Root module for `LipschitzMargin` — T1 (Tsuzuku–Sato–Sugiyama 2018) + T1′
(spectral-norm composition).  The Lipschitz-margin robustness certificate behind
`cnn.deep_contractive_cnn` and the margin half of the attention certificates.

See `LipschitzMargin/README.md` and prose/lipschitz-margin-certificate.md.
-/

import LipschitzMargin.Basic
import LipschitzMargin.DeepContractiveCNN
import LipschitzMargin.DeepContractiveCNNConcrete
import LipschitzMargin.DccnnLInfBox
