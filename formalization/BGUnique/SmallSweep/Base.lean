import BGUnique.StrictTable

namespace R3Cert
namespace SpiderStrict

/-- The sizes in 7..149 where the plain strict check does not apply (handled with exceptions). -/
def failSmall : List ℕ := [7, 8, 9, 11, 12, 13, 15, 16, 17, 19, 20, 21, 24, 28, 32]

/-- The plain strict check on a range, skipping the listed sizes. -/
def chunkOK (lo len : ℕ) : Bool := (List.range' lo len).all fun n => failSmall.contains n || checkNS n

theorem checkNS_of_chunk {lo len : ℕ} (h : chunkOK lo len = true) (n : ℕ) (h1 : lo ≤ n) (h2 : n < lo + len)
    (hn : n ∉ failSmall) : checkNS n = true := by
  unfold chunkOK at h
  rw [List.all_eq_true] at h
  have := h n (List.mem_range'_1.mpr ⟨h1, h2⟩)
  simpa [hn] using this

end SpiderStrict
end R3Cert
