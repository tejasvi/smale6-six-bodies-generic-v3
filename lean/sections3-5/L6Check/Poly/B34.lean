import L6Poly.Basic
import L6Check.Certs.Cbf128e8148a3614d

/-! Cofactor certificates, batch 34: `checkCert` of each embedded text (`native_decide`). -/

namespace L6.Poly.Checks

set_option maxHeartbeats 0 in
theorem cert_bf128e8148a3614d : L6.Poly.checkCert L6.Certs.Cbf128e8148a3614d = true := by native_decide

end L6.Poly.Checks
