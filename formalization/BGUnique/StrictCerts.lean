import Mathlib
import R3Cert.BGSpiderCandBase

namespace R3Cert
namespace SpiderStrict

open BGSpiderOpt BGSpiderRule BGSpiderCand

lemma key_lt {A1 A2 D1 D2 R1 R2 : ℚ} (h1 : 0 < D1) (h2 : 0 < D2)
    (h : A1 * (D1 + R1) * D2 < A2 * (D2 + R2) * D1) : A1 * (1 + R1 / D1) < A2 * (1 + R2 / D2) := by
  rw [show A1 * (1 + R1 / D1) = A1 * (D1 + R1) / D1 by field_simp,
    show A2 * (1 + R2 / D2) = A2 * (D2 + R2) / D2 by field_simp, div_lt_div_iff₀ h1 h2]
  linarith

/-- Strict form of `Φ_le_of_P`. -/
theorem Φ_lt_of_P (c a d k1 w4 w6 k2 m : ℕ) (hD1 : 0 < c + a + d + k1 + m)
    (hD2 : 0 < w4 + w6 + k2 + m) (hP : 0 < P c a d k1 w4 w6 k2 (m : ℚ)) :
    Φ c a (m + k1) d < Φ 0 w4 (m + k2) w6 := by
  have hD1' : (0 : ℚ) < (c : ℚ) + a + d + k1 + m := by exact_mod_cast hD1
  have hD2' : (0 : ℚ) < (w4 : ℚ) + w6 + k2 + m := by exact_mod_cast hD2
  have e1 : Φ c a (m + k1) d = G5 ^ m * ((3 / 2 : ℚ) ^ c * G4 ^ a * G5 ^ k1 * G6 ^ d *
      (1 + ((c : ℚ) / 3 + a * B4 + d * B6 + ((k1 : ℚ) + m) * B5) / ((c : ℚ) + a + d + k1 + m))) := by
    unfold Φ; rw [pow_add]; push_cast; ring
  have e2 : Φ 0 w4 (m + k2) w6 = G5 ^ m * (G4 ^ w4 * G5 ^ k2 * G6 ^ w6 *
      (1 + ((w4 : ℚ) * B4 + w6 * B6 + ((k2 : ℚ) + m) * B5) / ((w4 : ℚ) + w6 + k2 + m))) := by
    unfold Φ; rw [pow_add]; push_cast; ring
  rw [e1, e2]
  apply mul_lt_mul_of_pos_left _ (pow_pos G5_pos m)
  apply key_lt hD1' hD2'
  unfold P at hP
  linarith

lemma mono_pos {c0 c1 c2 t : ℚ} (h0 : 0 < c0) (h1 : 0 ≤ c1) (h2 : 0 ≤ c2) (ht : 0 ≤ t) :
    0 < c0 + c1 * t + c2 * t ^ 2 := by positivity

lemma bern_pos {b0 b1 b2 T t : ℚ} (h0 : 0 < b0) (h1 : 0 < b1) (h2 : 0 < b2) (hT : 0 < T) (ht : 0 ≤ t)
    (htT : t ≤ T) : 0 < b0 * (T - t) ^ 2 + b1 * (t * (T - t)) + b2 * t ^ 2 := by
  have hTt : 0 ≤ T - t := sub_nonneg.2 htT
  rcases eq_or_lt_of_le ht with h | h
  · subst h; simp only [sub_zero, zero_mul, mul_zero, add_zero, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow]; positivity
  · have : 0 < b2 * t ^ 2 := by positivity
    have : 0 ≤ b0 * (T - t) ^ 2 := by positivity
    have : 0 ≤ b1 * (t * (T - t)) := by positivity
    linarith

theorem strict_cert_1_Y (m : ℕ) (hm : 37 ≤ m) :
    Φ 0 10 (m + 0) 0 < Φ 0 0 (m + 7) 1 := by
  apply Φ_lt_of_P _ _ _ _ _ _ _ _ (by omega) (by omega)
  have key : ∀ t : ℚ, P 0 10 0 0 0 1 7 (37 + t) =
      (40250252194617694855825662204753 / 44255343017984000000000 : ℚ) + (8061664929380705806198466880681 / 110638357544960000000000 : ℚ) * t + (258412034876863778894124111321 / 221276715089920000000000 : ℚ) * t ^ 2 := by
    intro t; simp only [P, G4, G5, G6, B4, B5, B6]; push_cast; ring
  have hm' : (37 : ℚ) ≤ (m : ℚ) := by exact_mod_cast hm
  have e := key ((m : ℚ) - 37)
  rw [show (37 : ℚ) + ((m : ℚ) - 37) = m by ring] at e
  rw [e]
  exact mono_pos (by norm_num) (by norm_num) (by norm_num) (by linarith)

theorem strict_cert_2_Y (m : ℕ) (hm : 38 ≤ m) :
    Φ 0 9 (m + 0) 0 < Φ 0 0 (m + 5) 2 := by
  apply Φ_lt_of_P _ _ _ _ _ _ _ _ (by omega) (by omega)
  have key : ∀ t : ℚ, P 0 9 0 0 0 2 5 (38 + t) =
      (34394157456620246630952398271 / 968085628518400000000 : ℚ) + (4010419374382440999359743833 / 605053517824000000000 : ℚ) * t + (624631198693774217287613661 / 4840428142592000000000 : ℚ) * t ^ 2 := by
    intro t; simp only [P, G4, G5, G6, B4, B5, B6]; push_cast; ring
  have hm' : (38 : ℚ) ≤ (m : ℚ) := by exact_mod_cast hm
  have e := key ((m : ℚ) - 38)
  rw [show (38 : ℚ) + ((m : ℚ) - 38) = m by ring] at e
  rw [e]
  exact mono_pos (by norm_num) (by norm_num) (by norm_num) (by linarith)

theorem strict_cert_3_Y (m : ℕ) (hm : 60 ≤ m) :
    Φ 0 8 (m + 0) 0 < Φ 0 0 (m + 3) 3 := by
  apply Φ_lt_of_P _ _ _ _ _ _ _ _ (by omega) (by omega)
  have key : ∀ t : ℚ, P 0 8 0 0 0 3 3 (60 + t) =
      (3320456120941928512590477 / 6617772851200000000 : ℚ) + (10535095535315972544773271 / 13235545702400000000 : ℚ) * t + (1256697771743632254689601 / 105884365619200000000 : ℚ) * t ^ 2 := by
    intro t; simp only [P, G4, G5, G6, B4, B5, B6]; push_cast; ring
  have hm' : (60 : ℚ) ≤ (m : ℚ) := by exact_mod_cast hm
  have e := key ((m : ℚ) - 60)
  rw [show (60 : ℚ) + ((m : ℚ) - 60) = m by ring] at e
  rw [e]
  exact mono_pos (by norm_num) (by norm_num) (by norm_num) (by linarith)

theorem strict_cert_3_X (m : ℕ) (hm : 39 ≤ m) (hmU : m ≤ 59) :
    Φ 0 0 (m + 3) 3 < Φ 0 8 (m + 0) 0 := by
  apply Φ_lt_of_P _ _ _ _ _ _ _ _ (by omega) (by omega)
  have key : ∀ t : ℚ, P 0 0 3 3 8 0 0 (39 + t) =
      (232513006931814141400469571 / 8470749249536000000000 : ℚ) * (20 - t) ^ 2 + (24216298741889098582574817 / 605053517824000000000 : ℚ) * (t * (20 - t)) + (5979353715142658380409787 / 8470749249536000000000 : ℚ) * t ^ 2 := by
    intro t; simp only [P, G4, G5, G6, B4, B5, B6]; push_cast; ring
  have hm' : (39 : ℚ) ≤ (m : ℚ) := by exact_mod_cast hm
  have e := key ((m : ℚ) - 39)
  rw [show (39 : ℚ) + ((m : ℚ) - 39) = m by ring] at e
  rw [e]
  have hmU' : (m : ℚ) ≤ (59 : ℚ) := by exact_mod_cast hmU
  exact bern_pos (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by linarith) (by linarith)

theorem strict_cert_4_Y (m : ℕ) (hm : 206 ≤ m) :
    Φ 0 7 (m + 0) 0 < Φ 0 0 (m + 1) 4 := by
  apply Φ_lt_of_P _ _ _ _ _ _ _ _ (by omega) (by omega)
  have key : ∀ t : ℚ, P 0 7 0 0 0 4 1 (206 + t) =
      (90809703536898433679199 / 2316220497920000000 : ℚ) + (6954145958510301714489 / 57905512448000000 : ℚ) * t + (1312691969969263420641 / 2316220497920000000 : ℚ) * t ^ 2 := by
    intro t; simp only [P, G4, G5, G6, B4, B5, B6]; push_cast; ring
  have hm' : (206 : ℚ) ≤ (m : ℚ) := by exact_mod_cast hm
  have e := key ((m : ℚ) - 206)
  rw [show (206 : ℚ) + ((m : ℚ) - 206) = m by ring] at e
  rw [e]
  exact mono_pos (by norm_num) (by norm_num) (by norm_num) (by linarith)

theorem strict_cert_4_X (m : ℕ) (hm : 39 ≤ m) (hmU : m ≤ 205) :
    Φ 0 0 (m + 1) 4 < Φ 0 7 (m + 0) 0 := by
  apply Φ_lt_of_P _ _ _ _ _ _ _ _ (by omega) (by omega)
  have key : ∀ t : ℚ, P 0 0 4 1 7 0 0 (39 + t) =
      (1219152368604891185106309 / 7978221505085440000000 : ℚ) * (166 - t) ^ 2 + (1646850082719489166839771 / 2279491858595840000000 : ℚ) * (t * (166 - t)) + (4651086070838609286993 / 1595644301017088000000 : ℚ) * t ^ 2 := by
    intro t; simp only [P, G4, G5, G6, B4, B5, B6]; push_cast; ring
  have hm' : (39 : ℚ) ≤ (m : ℚ) := by exact_mod_cast hm
  have e := key ((m : ℚ) - 39)
  rw [show (39 : ℚ) + ((m : ℚ) - 39) = m by ring] at e
  rw [e]
  have hmU' : (m : ℚ) ≤ (205 : ℚ) := by exact_mod_cast hmU
  exact bern_pos (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by linarith) (by linarith)

theorem strict_cert_5_X (m : ℕ) (hm : 39 ≤ m) :
    Φ 0 0 (m + 0) 5 < Φ 0 6 (m + 1) 0 := by
  apply Φ_lt_of_P _ _ _ _ _ _ _ _ (by omega) (by omega)
  have key : ∀ t : ℚ, P 0 0 5 0 6 0 1 (39 + t) =
      (50715381799360263710691 / 5035261952000000 : ℚ) + (443434602631601747657961 / 1621354348544000000 : ℚ) * t + (1751983552315535638437 / 1621354348544000000 : ℚ) * t ^ 2 := by
    intro t; simp only [P, G4, G5, G6, B4, B5, B6]; push_cast; ring
  have hm' : (39 : ℚ) ≤ (m : ℚ) := by exact_mod_cast hm
  have e := key ((m : ℚ) - 39)
  rw [show (39 : ℚ) + ((m : ℚ) - 39) = m by ring] at e
  rw [e]
  exact mono_pos (by norm_num) (by norm_num) (by norm_num) (by linarith)

theorem strict_cert_6_X (m : ℕ) (hm : 38 ≤ m) :
    Φ 0 0 (m + 0) 6 < Φ 0 5 (m + 3) 0 := by
  apply Φ_lt_of_P _ _ _ _ _ _ _ _ (by omega) (by omega)
  have key : ∀ t : ℚ, P 0 0 6 0 5 0 3 (38 + t) =
      (79750806062095214711509311 / 394764537036800000 : ℚ) + (376918646827763956820289129 / 58109339851816960000 : ℚ) * t + (51426093800371756311957501 / 1162186797036339200000 : ℚ) * t ^ 2 := by
    intro t; simp only [P, G4, G5, G6, B4, B5, B6]; push_cast; ring
  have hm' : (38 : ℚ) ≤ (m : ℚ) := by exact_mod_cast hm
  have e := key ((m : ℚ) - 38)
  rw [show (38 : ℚ) + ((m : ℚ) - 38) = m by ring] at e
  rw [e]
  exact mono_pos (by norm_num) (by norm_num) (by norm_num) (by linarith)

theorem strict_cert_7_X (m : ℕ) (hm : 37 ≤ m) :
    Φ 0 0 (m + 0) 7 < Φ 0 4 (m + 5) 0 := by
  apply Φ_lt_of_P _ _ _ _ _ _ _ _ (by omega) (by omega)
  have key : ∀ t : ℚ, P 0 0 7 0 4 0 5 (37 + t) =
      (8507709622430415885479703041817 / 2263737761183825920000 : ℚ) + (27366498969404152161626646376959 / 208263874028911984640000 : ℚ) * t + (443757884886993845045552049999 / 416527748057823969280000 : ℚ) * t ^ 2 := by
    intro t; simp only [P, G4, G5, G6, B4, B5, B6]; push_cast; ring
  have hm' : (37 : ℚ) ≤ (m : ℚ) := by exact_mod_cast hm
  have e := key ((m : ℚ) - 37)
  rw [show (37 : ℚ) + ((m : ℚ) - 37) = m by ring] at e
  rw [e]
  exact mono_pos (by norm_num) (by norm_num) (by norm_num) (by linarith)

theorem strict_cert_8_X (m : ℕ) (hm : 36 ≤ m) :
    Φ 0 0 (m + 0) 8 < Φ 0 3 (m + 7) 0 := by
  apply Φ_lt_of_P _ _ _ _ _ _ _ _ (by omega) (by omega)
  have key : ∀ t : ℚ, P 0 0 8 0 3 0 7 (36 + t) =
      (5417148575210972443839457596491139 / 81132361360828320972800 : ℚ) + (6554437725169831286575208425806189 / 2665777587570073403392000 : ℚ) * t + (3243930994367961325595891507096001 / 149283544903924110589952000 : ℚ) * t ^ 2 := by
    intro t; simp only [P, G4, G5, G6, B4, B5, B6]; push_cast; ring
  have hm' : (36 : ℚ) ≤ (m : ℚ) := by exact_mod_cast hm
  have e := key ((m : ℚ) - 36)
  rw [show (36 : ℚ) + ((m : ℚ) - 36) = m by ring] at e
  rw [e]
  exact mono_pos (by norm_num) (by norm_num) (by norm_num) (by linarith)

theorem strict_cert_9_X (m : ℕ) (hm : 34 ≤ m) :
    Φ 0 0 (m + 0) 9 < Φ 0 2 (m + 9) 0 := by
  apply Φ_lt_of_P _ _ _ _ _ _ _ _ (by omega) (by omega)
  have key : ∀ t : ℚ, P 0 0 9 0 2 0 9 (34 + t) =
      (59198488243886577661510719832409469813237 / 53503222493566401235438796800 : ℚ) + (575606589753258322124365362989380399029 / 13375805623391600308859699200 : ℚ) * t + (21840222943225687727865457213281848799 / 53503222493566401235438796800 : ℚ) * t ^ 2 := by
    intro t; simp only [P, G4, G5, G6, B4, B5, B6]; push_cast; ring
  have hm' : (34 : ℚ) ≤ (m : ℚ) := by exact_mod_cast hm
  have e := key ((m : ℚ) - 34)
  rw [show (34 : ℚ) + ((m : ℚ) - 34) = m by ring] at e
  rw [e]
  exact mono_pos (by norm_num) (by norm_num) (by norm_num) (by linarith)

theorem strict_cert_10_X (m : ℕ) (hm : 33 ≤ m) :
    Φ 0 0 (m + 0) 10 < Φ 0 1 (m + 11) 0 := by
  apply Φ_lt_of_P _ _ _ _ _ _ _ _ (by omega) (by omega)
  have key : ∀ t : ℚ, P 0 0 10 0 1 0 11 (33 + t) =
      (356931420754137986350332836419811394537574749 / 19175554941694198202781264773120 : ℚ) + (1017212349281477389303349503822732782444279 / 1369682495835299871627233198080 : ℚ) * t + (139964243127447909572002038662552188197441 / 19175554941694198202781264773120 : ℚ) * t ^ 2 := by
    intro t; simp only [P, G4, G5, G6, B4, B5, B6]; push_cast; ring
  have hm' : (33 : ℚ) ≤ (m : ℚ) := by exact_mod_cast hm
  have e := key ((m : ℚ) - 33)
  rw [show (33 : ℚ) + ((m : ℚ) - 33) = m by ring] at e
  rw [e]
  exact mono_pos (by norm_num) (by norm_num) (by norm_num) (by linarith)

end SpiderStrict
end R3Cert
