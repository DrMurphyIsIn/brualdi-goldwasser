import R3Cert.BGEnvCert.G149.Common
import R3Cert.BGEnvCert.Force

namespace R3Cert.EnvCert.G149
open R3Cert.EnvCert

set_option maxRecDepth 100000 in
theorem sp_ok_9 : spidersOK phiTab spTab spM 125 137 = true := by decide +kernel

end R3Cert.EnvCert.G149
