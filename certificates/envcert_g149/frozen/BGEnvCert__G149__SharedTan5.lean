import R3Cert.BGEnvCert.G149.Common
import R3Cert.BGEnvCert.Force

namespace R3Cert.EnvCert.G149
open R3Cert.EnvCert

set_option maxRecDepth 100000 in
theorem tan_ok_5 : tanOK tanTab 25 30 = true := by decide +kernel

end R3Cert.EnvCert.G149
