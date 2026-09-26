/- Generated: kernel check of cap C = 12. -/
import R3Cert.BGEnvCert.G149.Common
import R3Cert.BGEnvCert.G149.Cap12

namespace R3Cert.EnvCert.G149
open R3Cert.EnvCert

set_option maxRecDepth 100000 in
theorem cap12_ok : capCheck tanTab ldTab phiTab cap12 = true := by decide +kernel

end R3Cert.EnvCert.G149
