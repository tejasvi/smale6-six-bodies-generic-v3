import L6Poly.Basic
import L6Check.Certs.C23a0171afb44fb7a

/-! Cofactor certificates, batch 4: `checkCert` of each embedded text (`native_decide`). -/

namespace L6.Poly.Checks

set_option maxHeartbeats 0 in
theorem cert_23a0171afb44fb7a : L6.Poly.checkCert L6.Certs.C23a0171afb44fb7a = true := by native_decide

end L6.Poly.Checks
