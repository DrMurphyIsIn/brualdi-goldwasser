import R3Cert.BGEnvCert.G149.SharedTan0
import R3Cert.BGEnvCert.G149.SharedTan1
import R3Cert.BGEnvCert.G149.SharedTan2
import R3Cert.BGEnvCert.G149.SharedTan3
import R3Cert.BGEnvCert.G149.SharedTan4
import R3Cert.BGEnvCert.G149.SharedTan5
import R3Cert.BGEnvCert.G149.SharedTan6
import R3Cert.BGEnvCert.G149.SharedTan7
import R3Cert.BGEnvCert.G149.SharedTan8
import R3Cert.BGEnvCert.G149.SharedTan9
import R3Cert.BGEnvCert.G149.SharedTan10
import R3Cert.BGEnvCert.G149.SharedTan11
import R3Cert.BGEnvCert.G149.SharedTan12
import R3Cert.BGEnvCert.G149.SharedTan13
import R3Cert.BGEnvCert.G149.SharedTan14
import R3Cert.BGEnvCert.G149.SharedTan15
import R3Cert.BGEnvCert.G149.SharedTan16
import R3Cert.BGEnvCert.G149.SharedTan17
import R3Cert.BGEnvCert.G149.SharedTan18
import R3Cert.BGEnvCert.G149.SharedTan19
import R3Cert.BGEnvCert.G149.SharedLd
import R3Cert.BGEnvCert.G149.SharedSp0
import R3Cert.BGEnvCert.G149.SharedSp1
import R3Cert.BGEnvCert.G149.SharedSp2
import R3Cert.BGEnvCert.G149.SharedSp3
import R3Cert.BGEnvCert.G149.SharedSp4
import R3Cert.BGEnvCert.G149.SharedSp5
import R3Cert.BGEnvCert.G149.SharedSp6
import R3Cert.BGEnvCert.G149.SharedSp7
import R3Cert.BGEnvCert.G149.SharedSp8
import R3Cert.BGEnvCert.G149.SharedSp9
import R3Cert.BGEnvCert.G149.SharedSp10

namespace R3Cert.EnvCert.G149
open R3Cert.EnvCert

theorem tan_ok : tanOK tanTab 0 HG = true := by
  have h0 := tan_ok_0
  have h1 := tanOK_split tanTab 0 5 10 (by omega) (by omega) h0 tan_ok_1
  have h2 := tanOK_split tanTab 0 10 15 (by omega) (by omega) h1 tan_ok_2
  have h3 := tanOK_split tanTab 0 15 20 (by omega) (by omega) h2 tan_ok_3
  have h4 := tanOK_split tanTab 0 20 25 (by omega) (by omega) h3 tan_ok_4
  have h5 := tanOK_split tanTab 0 25 30 (by omega) (by omega) h4 tan_ok_5
  have h6 := tanOK_split tanTab 0 30 35 (by omega) (by omega) h5 tan_ok_6
  have h7 := tanOK_split tanTab 0 35 40 (by omega) (by omega) h6 tan_ok_7
  have h8 := tanOK_split tanTab 0 40 45 (by omega) (by omega) h7 tan_ok_8
  have h9 := tanOK_split tanTab 0 45 50 (by omega) (by omega) h8 tan_ok_9
  have h10 := tanOK_split tanTab 0 50 55 (by omega) (by omega) h9 tan_ok_10
  have h11 := tanOK_split tanTab 0 55 60 (by omega) (by omega) h10 tan_ok_11
  have h12 := tanOK_split tanTab 0 60 65 (by omega) (by omega) h11 tan_ok_12
  have h13 := tanOK_split tanTab 0 65 70 (by omega) (by omega) h12 tan_ok_13
  have h14 := tanOK_split tanTab 0 70 75 (by omega) (by omega) h13 tan_ok_14
  have h15 := tanOK_split tanTab 0 75 80 (by omega) (by omega) h14 tan_ok_15
  have h16 := tanOK_split tanTab 0 80 85 (by omega) (by omega) h15 tan_ok_16
  have h17 := tanOK_split tanTab 0 85 90 (by omega) (by omega) h16 tan_ok_17
  have h18 := tanOK_split tanTab 0 90 95 (by omega) (by omega) h17 tan_ok_18
  have h19 := tanOK_split tanTab 0 95 100 (by omega) (by omega) h18 tan_ok_19
  exact h19

theorem spiders_ok : spidersOK phiTab spTab spM 7 149 = true := by
  have g0 := sp_ok_0
  have g1 := spidersOK_split phiTab spTab spM 7 20 33 (by omega) (by omega) g0 sp_ok_1
  have g2 := spidersOK_split phiTab spTab spM 7 33 46 (by omega) (by omega) g1 sp_ok_2
  have g3 := spidersOK_split phiTab spTab spM 7 46 59 (by omega) (by omega) g2 sp_ok_3
  have g4 := spidersOK_split phiTab spTab spM 7 59 72 (by omega) (by omega) g3 sp_ok_4
  have g5 := spidersOK_split phiTab spTab spM 7 72 85 (by omega) (by omega) g4 sp_ok_5
  have g6 := spidersOK_split phiTab spTab spM 7 85 98 (by omega) (by omega) g5 sp_ok_6
  have g7 := spidersOK_split phiTab spTab spM 7 98 111 (by omega) (by omega) g6 sp_ok_7
  have g8 := spidersOK_split phiTab spTab spM 7 111 124 (by omega) (by omega) g7 sp_ok_8
  have g9 := spidersOK_split phiTab spTab spM 7 124 137 (by omega) (by omega) g8 sp_ok_9
  have g10 := spidersOK_split phiTab spTab spM 7 137 149 (by omega) (by omega) g9 sp_ok_10
  exact g10

end R3Cert.EnvCert.G149
