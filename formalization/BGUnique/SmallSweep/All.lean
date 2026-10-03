import BGUnique.SmallSweep.C_0
import BGUnique.SmallSweep.C_1
import BGUnique.SmallSweep.C_2
import BGUnique.SmallSweep.C_3
import BGUnique.SmallSweep.C_4
import BGUnique.SmallSweep.C_5
import BGUnique.SmallSweep.C_6
import BGUnique.SmallSweep.C_7
import BGUnique.SmallSweep.C_8
import BGUnique.SmallSweep.C_9
import BGUnique.SmallSweep.C_10

namespace R3Cert
namespace SpiderStrict

/-- The plain strict check holds for every `7 ≤ n ≤ 149` outside `failSmall`. -/
theorem checkNS_small (n : ℕ) (h7 : 7 ≤ n) (h149 : n ≤ 149) (hn : n ∉ failSmall) : checkNS n = true := by
  by_cases hc0 : n < 20
  · exact checkNS_of_chunk chunk_0 n (by omega) (by omega) hn
  by_cases hc1 : n < 33
  · exact checkNS_of_chunk chunk_1 n (by omega) (by omega) hn
  by_cases hc2 : n < 46
  · exact checkNS_of_chunk chunk_2 n (by omega) (by omega) hn
  by_cases hc3 : n < 59
  · exact checkNS_of_chunk chunk_3 n (by omega) (by omega) hn
  by_cases hc4 : n < 72
  · exact checkNS_of_chunk chunk_4 n (by omega) (by omega) hn
  by_cases hc5 : n < 85
  · exact checkNS_of_chunk chunk_5 n (by omega) (by omega) hn
  by_cases hc6 : n < 98
  · exact checkNS_of_chunk chunk_6 n (by omega) (by omega) hn
  by_cases hc7 : n < 111
  · exact checkNS_of_chunk chunk_7 n (by omega) (by omega) hn
  by_cases hc8 : n < 124
  · exact checkNS_of_chunk chunk_8 n (by omega) (by omega) hn
  by_cases hc9 : n < 137
  · exact checkNS_of_chunk chunk_9 n (by omega) (by omega) hn
  by_cases hc10 : n < 150
  · exact checkNS_of_chunk chunk_10 n (by omega) (by omega) hn
  omega

end SpiderStrict
end R3Cert
