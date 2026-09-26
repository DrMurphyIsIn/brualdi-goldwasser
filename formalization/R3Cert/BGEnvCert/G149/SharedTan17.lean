import R3Cert.BGEnvCert.G149.Common
import R3Cert.BGEnvCert.Force

namespace R3Cert.EnvCert.G149
open R3Cert.EnvCert

set_option maxRecDepth 100000 in
theorem tan_ok_17 : tanOK tanTab 85 90 = true := by decide +kernel

end R3Cert.EnvCert.G149
