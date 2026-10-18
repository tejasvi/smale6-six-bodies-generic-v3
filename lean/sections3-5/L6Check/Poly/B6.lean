import L6Poly.Basic
import L6Check.Certs.C256f9e3729faae4e

/-! Cofactor certificates, batch 6: `checkCert` of each embedded text (`native_decide`). -/

namespace L6.Poly.Checks

set_option maxHeartbeats 0 in
theorem cert_256f9e3729faae4e : L6.Poly.checkCert L6.Certs.C256f9e3729faae4e = true := by native_decide

end L6.Poly.Checks
