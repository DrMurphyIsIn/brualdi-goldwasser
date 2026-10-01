/- Comparator challenge, one-block part 1 (imports only Mathlib): planted branch = finite rooted (rose)
   tree; |b| = number of vertices. Kept in its own module so that the auxiliary matcher names coincide with the
   solution's. -/
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
