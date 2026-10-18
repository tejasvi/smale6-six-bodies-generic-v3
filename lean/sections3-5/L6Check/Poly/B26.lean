import L6Poly.Basic
import L6Check.Certs.C8bec77cf6509c4bc

/-! Cofactor certificates, batch 26: `checkCert` of each embedded text (`native_decide`). -/

namespace L6.Poly.Checks

set_option maxHeartbeats 0 in
theorem cert_8bec77cf6509c4bc : L6.Poly.checkCert L6.Certs.C8bec77cf6509c4bc = true := by native_decide

end L6.Poly.Checks
