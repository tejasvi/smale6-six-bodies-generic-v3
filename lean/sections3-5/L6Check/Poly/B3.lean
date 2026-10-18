import L6Poly.Basic
import L6Check.Certs.C19766c038a4f930e

/-! Cofactor certificates, batch 3: `checkCert` of each embedded text (`native_decide`). -/

namespace L6.Poly.Checks

set_option maxHeartbeats 0 in
theorem cert_19766c038a4f930e : L6.Poly.checkCert L6.Certs.C19766c038a4f930e = true := by native_decide

end L6.Poly.Checks
