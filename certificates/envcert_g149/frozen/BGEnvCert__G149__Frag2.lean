/- Generated: kernel check of cap C = 2. -/
import R3Cert.BGEnvCert.G149.Common
import R3Cert.BGEnvCert.G149.Cap2

namespace R3Cert.EnvCert.G149
open R3Cert.EnvCert

set_option maxRecDepth 100000 in
theorem cap2_ok : capCheck tanTab ldTab phiTab cap2 = true := by decide +kernel

end R3Cert.EnvCert.G149
