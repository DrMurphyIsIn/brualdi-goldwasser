import R3Cert.BGEnvCert.G149.Common
import R3Cert.BGEnvCert.Force

namespace R3Cert.EnvCert.G149
open R3Cert.EnvCert

set_option maxRecDepth 100000 in
theorem sp_ok_0 : spidersOK phiTab spTab spM 7 20 = true := by decide +kernel

end R3Cert.EnvCert.G149
