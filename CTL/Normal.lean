import TS.Basic
import CTL.Basic
import CTL.Satisfaction

namespace CTL

inductive ENF where
  | top          : ENF
  | prop         : P   → ENF
  | conj         : ENF → ENF → ENF
  | neg          : ENF → ENF
  | exist_next   : ENF → ENF
  | exist_untl   : ENF → ENF → ENF
  | exist_always : ENF → ENF

end CTL
