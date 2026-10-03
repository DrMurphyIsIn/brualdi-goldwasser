L_Y={1:37,2:38,3:60,4:206}
out=[]
def eqcontra():
    return "    exact absurd ⟨h4.symm, h5.symm, h6.symm⟩ hne"
# a = 0, d = s : l is Y_s ; also s = 0 (a = d = 0)
for s in range(0,11):
    N=f"(1 + 9 * 0 + 11 * b + 13 * {s})"
    L=[f"theorem scombo_0_{s} (b : ℕ) (hn : 492 ≤ {N})",
       f"    (hne : ¬ (0 = w4 {N} ∧ b = w5 {N} ∧ {s} = w6 {N})) :",
       f"    Φ 0 0 b {s} < Φ 0 (w4 {N}) (w5 {N}) (w6 {N}) := by",
       f"  have hs : sres {N} = {s} := by unfold sres; omega"]
    def yeq(src):
        return [f"  {src}",
                f"    have h4 : w4 {N} = 0 := by have := hw.1; omega",
                f"    have h6 : w6 {N} = {s} := by have := hw.2; omega",
                f"    have h5 : w5 {N} = b := by unfold w5; rw [h4, h6]; omega",
                eqcontra()]
    if s==0:
        L+=[f"  have hw := w_zero _ hs",
            f"  have h4 : w4 {N} = 0 := by have := hw.1; omega",
            f"  have h6 : w6 {N} = 0 := by have := hw.2; omega",
            f"  have h5 : w5 {N} = b := by unfold w5; rw [h4, h6]; omega",
            f"  exact absurd ⟨h4.symm, h5.symm, h6.symm⟩ hne"]
    elif s<=2:
        L+=[f"  have hw := w_six _ {s} hs (by omega) (by omega) (by omega)",
            f"  have h4 : w4 {N} = 0 := by have := hw.1; omega",
            f"  have h6 : w6 {N} = {s} := by have := hw.2; omega",
            f"  have h5 : w5 {N} = b := by unfold w5; rw [h4, h6]; omega",
            f"  exact absurd ⟨h4.symm, h5.symm, h6.symm⟩ hne"]
    elif s in (3,4):
        thr = 723 if s==3 else 2320
        k1 = 9-2*s
        L+=[f"  rcases Nat.lt_or_ge {N} {thr} with hlo | hhi",
            f"  · have hw := w_four _ {s} hs (by omega) (by omega)",
            f"    obtain ⟨m, rfl⟩ : ∃ m, b = m + {k1} := ⟨b - {k1}, by omega⟩",
            f"    have h4 : w4 (1 + 9 * 0 + 11 * (m + {k1}) + 13 * {s}) = {11-s} := by have := hw.1; omega",
            f"    have h6 : w6 (1 + 9 * 0 + 11 * (m + {k1}) + 13 * {s}) = 0 := by have := hw.2; omega",
            f"    have h5 : w5 (1 + 9 * 0 + 11 * (m + {k1}) + 13 * {s}) = m + 0 := by unfold w5; rw [h4, h6]; omega",
            f"    rw [h4, h5, h6]",
            f"    exact strict_cert_{s}_X m (by omega) (by omega)",
            f"  · have hw := w_six _ {s} hs (by omega) (by omega) (by omega)",
            f"    have h4 : w4 {N} = 0 := by have := hw.1; omega",
            f"    have h6 : w6 {N} = {s} := by have := hw.2; omega",
            f"    have h5 : w5 {N} = b := by unfold w5; rw [h4, h6]; omega",
            f"    exact absurd ⟨h4.symm, h5.symm, h6.symm⟩ hne"]
    else:
        k2=2*s-9
        L+=[f"  have hw := w_four _ {s} hs (by omega) (by omega)",
            f"  have h4 : w4 {N} = {11-s} := by have := hw.1; omega",
            f"  have h6 : w6 {N} = 0 := by have := hw.2; omega",
            f"  have h5 : w5 {N} = b + {k2} := by unfold w5; rw [h4, h6]; omega",
            f"  rw [h4, h5, h6]",
            f"  exact strict_cert_{s}_X b (by omega)"]
    out.append("\n".join(L)+"\n")
# d = 0, a = 11 - s (s = 1..10): l is X_s
for s in range(1,11):
    a=11-s; N=f"(1 + 9 * {a} + 11 * b + 13 * 0)"
    L=[f"theorem scombo_{a}_0 (b : ℕ) (hn : 492 ≤ {N})",
       f"    (hne : ¬ ({a} = w4 {N} ∧ b = w5 {N} ∧ 0 = w6 {N})) :",
       f"    Φ 0 {a} b 0 < Φ 0 (w4 {N}) (w5 {N}) (w6 {N}) := by",
       f"  have hs : sres {N} = {s} := by unfold sres; omega"]
    def xeq(ind):
        return [f"{ind}have hw := w_four _ {s} hs (by omega) (by omega)",
                f"{ind}have h4 : w4 {N} = {a} := by have := hw.1; omega",
                f"{ind}have h6 : w6 {N} = 0 := by have := hw.2; omega",
                f"{ind}have h5 : w5 {N} = b := by unfold w5; rw [h4, h6]; omega",
                f"{ind}exact absurd ⟨h4.symm, h5.symm, h6.symm⟩ hne"]
    def ywin(ind):
        return [f"{ind}have hw := w_six _ {s} hs (by omega) (by omega) (by omega)",
                f"{ind}have h4 : w4 {N} = 0 := by have := hw.1; omega",
                f"{ind}have h6 : w6 {N} = {s} := by have := hw.2; omega",
                f"{ind}have h5 : w5 {N} = b + {9-2*s} := by unfold w5; rw [h4, h6]; omega",
                f"{ind}rw [h4, h5, h6]",
                f"{ind}exact strict_cert_{s}_Y b (by omega)"]
    if s<=2: L+=ywin("  ")
    elif s in (3,4):
        thr = 723 if s==3 else 2320
        L+=[f"  rcases Nat.lt_or_ge {N} {thr} with hlo | hhi"]
        L+=["  · "+xeq("    ")[0].strip()]+xeq("    ")[1:]
        L+=["  · "+ywin("    ")[0].strip()]+ywin("    ")[1:]
    else: L+=xeq("  ")
    out.append("\n".join(L)+"\n")
open('BGUnique/Combos.body','w').write("\n".join(out))
print(len(out))
