import L6Poly.Basic
import L6Check.Certs.C6854bcb779f23df6

/-! Cofactor certificates, batch 20: `checkCert` of each embedded text (`native_decide`). -/

namespace L6.Poly.Checks

set_option maxHeartbeats 0 in
theorem cert_6854bcb779f23df6 : L6.Poly.checkCert L6.Certs.C6854bcb779f23df6 = true := by native_decide

end L6.Poly.Checks
