/-
  R3Cert.BGAnswer -- the answer, as data: the children of the maximizer's centre.

  `bgChildren n` is the table spider `tab n` for n <= 491 and the rule spider `W n` beyond.  Kept in its
  own small module so that the Comparator challenge (`comparator/BGChallenge.lean`) can state the theorem
  without importing its proof.
-/
import Mathlib
import R3Cert.BGSpiderTableData

namespace R3Cert
namespace BGStatement

open BGSpiderOpt BGSpiderRule BGSpiderTable

/-- The children of the maximizer's centre. -/
def bgChildren (n : ℕ) : List Child := if n ≤ 491 then tab n else W n

end BGStatement
end R3Cert
