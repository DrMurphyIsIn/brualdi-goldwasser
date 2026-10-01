/- Comparator challenge, part 1 (imports only Mathlib): planted branches as finite rooted (rose) trees, and
   their vertex count |b|. Kept in its own module so that the auxiliary matchers get the same names as in the
   solution. -/
import Mathlib

namespace LeanCherry

inductive Br where
  | node : List Br → Br

namespace Br

mutual
def size : Br → ℕ
  | .node cs => sizeL cs + 1
def sizeL : List Br → ℕ
  | [] => 0
  | c :: cs => size c + sizeL cs
end

end Br

end LeanCherry
